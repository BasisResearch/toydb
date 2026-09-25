-------------------------------- MODULE Raft --------------------------------
(***************************************************************************)
(* A faithful transliteration of toyDB's Verus Raft protocol model,        *)
(* `src/raft/safety.rs`, into TLA+ for model checking with TLC.            *)
(*                                                                         *)
(* Naming is deliberately identical to the Rust: every `t_*` transition,   *)
(* every `inv_*` conjunct and every spec helper keeps its Rust name, so an *)
(* agent can move between the two files line by line.  Structure follows   *)
(* the Rust conjunct-by-conjunct, in the same order.                       *)
(*                                                                         *)
(* SEQUENCE INDEXING.  Verus `Seq<AEntry>` is 0-based and its element k    *)
(* models implementation index k+1.  TLA+ sequences are 1-based, so this   *)
(* module uses TLA+ index k+1 wherever the Rust writes `log[k]`, i.e. the  *)
(* TLA+ index *is* the implementation index.  Concretely: Rust            *)
(* `h.log[b - 1].term` becomes `h.log[b].term`, Rust                      *)
(* `log.subrange(b, e)` becomes `SubSeq(log, b+1, e)`, and Rust           *)
(* `ll[elog.len()].term` becomes `ll[Len(elog)+1].term`.  All `nat`-valued *)
(* index parameters (b, e, mi, ci, base) keep exactly the Rust meaning:    *)
(* they are prefix *lengths*, not positions.                               *)
(*                                                                         *)
(* APPROXIMATIONS.  Collected here, and repeated at each site:             *)
(*                                                                         *)
(*  (A1) `GState.n` is the constant N rather than a state field.  Every    *)
(*       transition asserts `post.n == pre.n` and `init` asserts           *)
(*       `s.n >= 1`, so n is constant along every execution; making it a   *)
(*       constant loses no behaviour.                                      *)
(*  (A2) `Option<Seq<u8>>` commands are abstracted to the finite constant  *)
(*       set `Command` (plus `Nil` for `None`, the election noop).  The    *)
(*       model never inspects a command's bytes -- `cmd` occurs only in    *)
(*       entry equality -- so any two-or-more-element set is as            *)
(*       discriminating as `Seq<u8>`.                                      *)
(*  (A3) The five unbounded-growth transitions carry the bound in their    *)
(*       guard, not only in the state constraint: `t_bump_term` picks      *)
(*       `t \in (h.term+1)..MaxTerm`; `t_campaign` requires                *)
(*       `h.term < MaxTerm`; `t_become_leader` and `t_propose` require     *)
(*       `Len(h.log) < MaxLog`; `t_submit_read` requires                   *)
(*       `h.read_seq < MaxRead`.  The set of states TLC *explores* is      *)
(*       identical to what CONSTRAINT alone would give, because a state    *)
(*       the constraint excludes is never enqueued.  The guards are        *)
(*       needed because TLC evaluates the invariants on a successor        *)
(*       *before* applying the constraint (ModelChecker.doNext: `unseen`   *)
(*       is true when `inModel` is false), so a one-step-past-the-bound    *)
(*       successor would be type-checked against domains that do not       *)
(*       contain it.  CONSTRAINT is kept as well, as the declarative       *)
(*       statement of the bounds.                                          *)
(*  (A4) `t_leader_commit` quantifies the ack map `q` over                 *)
(*       `[Q -> 0..MaxLog]` rather than over all `Map<int,nat>`.  Its      *)
(*       guard requires `Msg::Ack{v, term, mi: q[v]}` in `net`, and        *)
(*       `ack_msg_ok` bounds every ack's `mi` by a leader log length,      *)
(*       which the constraint bounds by MaxLog; so no `q` is lost.         *)
(*  (A5) Verus `Map` is total: `m[t]` for `t` outside `m.dom()` is an      *)
(*       unspecified but fixed value.  TLA+ function application outside   *)
(*       the domain is undefined and TLC errors on it.  Where the Rust     *)
(*       indexes a map without a locally visible domain guard (always      *)
(*       `leader_log` or `leader_of`; the guard lives in a sibling         *)
(*       conjunct), this module reads through `LL(t)` / `LOf(t)`, which    *)
(*       return the empty log / node 0 off-domain.  On states where the    *)
(*       sibling conjunct holds -- which is every reachable state -- this  *)
(*       is exactly the Rust.  Off-domain, the Rust's value is arbitrary   *)
(*       and ours is a specific choice; the difference is unobservable in  *)
(*       the Verus proof for the same reason.                              *)
(*  (A6) Parameters the Rust obtains by `pre.net.contains(Msg::X{..})` are *)
(*       bound here by `\E m \in net : m.kind = "X" /\ ...` instead of by  *)
(*       an unbounded existential plus a membership guard.  These are      *)
(*       logically identical; the message-set form is what TLC can         *)
(*       enumerate.                                                        *)
(*  (A7) The network is monotone -- `net` only ever grows -- so the number *)
(*       of reachable `net` values is what makes the model blow up.        *)
(*       CONSTRAINT bounds `Cardinality(net)` by MaxMsgs.  Unlike (A3)     *)
(*       this one needs no action-level guard: every `inv_*` conjunct and  *)
(*       TypeOK hold on the one-message-past-the-bound successors TLC      *)
(*       evaluates them on, because they hold on every state reachable     *)
(*       from `init` regardless of bounds.  It does truncate behaviours:   *)
(*       traces that need more than MaxMsgs messages in flight are not     *)
(*       explored, so this is a bounded check, not a proof.                *)
(*                                                                         *)
(* Nothing else was simplified: the ghost payloads (`clog`, `vlog`,        *)
(* `rec`), the ghost maps (`leader_log`, `leader_of`, `voters`,            *)
(* `elect_log`, `elect_votes`, `read_hwm`) and the ghost sets (`commits`,  *)
(* `reads`, with `ReadRec.born` a set of commit records) are all carried,  *)
(* because the `inv_*` conjuncts refer to them.                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,        \* cluster size; GState.n (A1)
    MaxTerm,  \* term bound, enforced by Constraint
    MaxLog,   \* log-length bound, enforced by Constraint
    MaxRead,  \* read-sequence bound, enforced by Constraint (A3)
    MaxMsgs,  \* |net| bound, enforced by Constraint (A7)
    Command,  \* the abstract command alphabet, standing for Seq<u8> (A2)
    Nil       \* the None of Option<int> / Option<Seq<u8>>

VARIABLES
    hosts,        \* GState.hosts : [Node -> MHost]
    net,          \* GState.net   : monotone set of Msg
    leader_log,   \* GState.leader_log
    leader_of,    \* GState.leader_of
    voters,       \* GState.voters
    elect_log,    \* GState.elect_log
    elect_votes,  \* GState.elect_votes
    commits,      \* GState.commits
    reads,        \* GState.reads
    read_hwm      \* GState.read_hwm

vars == << hosts, net, leader_log, leader_of, voters, elect_log, elect_votes,
           commits, reads, read_hwm >>

ghost_vars == << leader_log, leader_of, voters, elect_log, elect_votes,
                 commits, reads, read_hwm >>

\* ---------------------------------------------------------------------------
\* Verus Map / Set plumbing
\* ---------------------------------------------------------------------------

\* Map::empty(); the empty TLA+ function.
EmptyFn == << >>

\* Map::insert(k, v).
Ins(f, k, v) == [x \in (DOMAIN f) \cup {k} |-> IF x = k THEN v ELSE f[x]]

\* Total-map reads for leader_log / leader_of; see approximation (A5).
LL(t)  == IF t \in DOMAIN leader_log THEN leader_log[t] ELSE << >>
LOf(t) == IF t \in DOMAIN leader_of  THEN leader_of[t]  ELSE 0

\* Total-map read of an arbitrary term-indexed log map, for mid_compliant.
At(m, t) == IF t \in DOMAIN m THEN m[t] ELSE << >>

\* ---------------------------------------------------------------------------
\* Spec helpers  (safety.rs "Spec helpers")
\* ---------------------------------------------------------------------------

\* node_ids(n)
node_ids == 0 .. (N - 1)
Node == node_ids

\* is_quorum(n, q): a strict majority (RawNode::quorum_size).
is_quorum(q) == q \subseteq node_ids /\ 2 * Cardinality(q) > N

\* last_term(log): the term of the last entry, 0 for an empty log.
last_term(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)].term

\* up_to_date(a, b): the section 5.4.1 check, `a` at least as up-to-date as `b`.
up_to_date(a, b) ==
    \/ last_term(a) > last_term(b)
    \/ (last_term(a) = last_term(b) /\ Len(a) >= Len(b))

\* prefix_eq(a, b, i): the first i entries of a and b exist and agree.
prefix_eq(a, b, i) ==
    /\ i <= Len(a)
    /\ i <= Len(b)
    /\ \A j \in 1 .. i : a[j] = b[j]

\* splice_is_noop(log, base, entries)
splice_is_noop(log, base, entries) ==
    /\ base + Len(entries) <= Len(log)
    /\ \A j \in 1 .. Len(entries) : log[base + j] = entries[j]

\* splice(log, base, entries): the result of Log::splice.
splice(log, base, entries) ==
    IF splice_is_noop(log, base, entries)
    THEN log
    ELSE SubSeq(log, 1, base) \o entries

\* pinned_at(m, log, j): entry j pins log's prefix through j to m[log[j].term].
pinned_at(m, log, j) ==
    LET t == log[j].term
    IN  /\ t \in DOMAIN m
        /\ j <= Len(m[t])
        /\ \A k \in 1 .. j : log[k] = m[t][k]

\* log_pinned(m, log)
log_pinned(m, log) == \A j \in 1 .. Len(log) : pinned_at(m, log, j)

\* log_wf(log): terms >= 1 and nondecreasing.
log_wf(log) ==
    /\ \A j \in 1 .. Len(log) : log[j].term >= 1
    /\ \A j1 \in 1 .. Len(log) : \A j2 \in 1 .. Len(log) :
           j1 <= j2 => log[j1].term <= log[j2].term

\* terms_le(log, t) / terms_lt(log, t)
terms_le(log, t) == \A j \in 1 .. Len(log) : log[j].term <= t
terms_lt(log, t) == \A j \in 1 .. Len(log) : log[j].term <  t

\* mid_compliant(m, t, ub, i): leader logs of elected terms strictly between
\* t and ub agree with m[t] on the first i entries.  m[t] read via At (A5).
mid_compliant(m, t, ub, i) ==
    \A x \in DOMAIN m : (t < x /\ x < ub) => prefix_eq(m[x], At(m, t), i)

\* ---------------------------------------------------------------------------
\* Message constructors (Msg's variants, with their ghost payloads)
\* ---------------------------------------------------------------------------

MCampaign(c, t, clog)    == [kind |-> "Campaign",    c |-> c, term |-> t, clog |-> clog]
MVote(v, c, t, vlog)     == [kind |-> "Vote",        v |-> v, c |-> c, term |-> t, vlog |-> vlog]
MAppend(t, b, bt, es)    == [kind |-> "Append",      term |-> t, base |-> b, bterm |-> bt, entries |-> es]
MCommit(t, ci, rec)      == [kind |-> "Commit",      term |-> t, ci |-> ci, rec |-> rec]
MAck(v, t, mi)           == [kind |-> "Ack",         v |-> v, term |-> t, mi |-> mi]
MRead(t, sq)             == [kind |-> "Read",        term |-> t, seq |-> sq]
MReadConfirm(v, t, sq)   == [kind |-> "ReadConfirm", v |-> v, term |-> t, seq |-> sq]

\* ---------------------------------------------------------------------------
\* Frame conditions  (unch_ghost / unch_elect / unch_reads)
\* ---------------------------------------------------------------------------

unch_ghost == UNCHANGED ghost_vars
unch_elect == UNCHANGED << leader_of, voters, elect_log, elect_votes >>
unch_reads == UNCHANGED << reads, read_hwm >>

\* ---------------------------------------------------------------------------
\* Transitions  (safety.rs "Transitions")
\* ---------------------------------------------------------------------------

\* t_campaign(pre, post, i): RawNode::<Candidate>::campaign.  Bump the term,
\* vote for self, solicit votes; the self-vote is a Vote message.
t_campaign(i) ==
    LET h == hosts[i]
        t == h.term + 1
    IN  /\ h.role # "Leader"                     \* leaders never campaign
        /\ h.term < MaxTerm                       \* bound, see (A3)
        /\ hosts' = [hosts EXCEPT ![i] =
               [h EXCEPT !.term = t, !.vote = i, !.role = "Candidate",
                         !.votes = {i}, !.vote_logs = Ins(EmptyFn, i, h.log)]]
        /\ net' = net \cup { MCampaign(i, t, h.log), MVote(i, i, t, h.log) }
        /\ unch_ghost

\* t_grant(pre, post, v, c, t, clog): Message::Campaign handling.  (c, t, clog)
\* come from the Campaign message in net (A6).
t_grant(v) ==
    \E m \in net :
        /\ m.kind = "Campaign"
        /\ LET h == hosts[v]
               c == m.c
               t == m.term
               clog == m.clog
           IN  /\ v # c
               /\ t >= h.term
               /\ (t = h.term => (h.role = "Follower" /\ (h.vote = Nil \/ h.vote = c)))
               /\ up_to_date(clog, h.log)
               /\ hosts' = [hosts EXCEPT ![v] =
                      [h EXCEPT !.term = t, !.vote = c, !.role = "Follower"]]
               /\ net' = net \cup { MVote(v, c, t, h.log) }
               /\ unch_ghost

\* t_collect_vote(pre, post, i, v, vlog): Message::CampaignResponse handling.
\* (v, vlog) come from the Vote message in net (A6).
t_collect_vote(i) ==
    LET h == hosts[i]
    IN  /\ h.role = "Candidate"
        /\ \E m \in net :
               /\ m.kind = "Vote"
               /\ m.c = i
               /\ m.term = h.term
               /\ hosts' = [hosts EXCEPT ![i] =
                      [h EXCEPT !.votes = h.votes \cup {m.v},
                                !.vote_logs = Ins(h.vote_logs, m.v, m.vlog)]]
        /\ UNCHANGED net
        /\ unch_ghost

\* t_become_leader(pre, post, i): Candidate::into_leader, incl. the noop append.
t_become_leader(i) ==
    LET h == hosts[i]
        newlog == Append(h.log, [term |-> h.term, cmd |-> Nil])
    IN  /\ h.role = "Candidate"
        /\ is_quorum(h.votes)
        /\ Len(h.log) < MaxLog                    \* bound, see (A3)
        /\ hosts' = [hosts EXCEPT ![i] =
               [h EXCEPT !.role = "Leader", !.log = newlog, !.read_seq = 0]]
        /\ UNCHANGED net
        /\ leader_log'  = Ins(leader_log,  h.term, newlog)
        /\ leader_of'   = Ins(leader_of,   h.term, i)
        /\ voters'      = Ins(voters,      h.term, h.votes)
        /\ elect_log'   = Ins(elect_log,   h.term, h.log)
        /\ elect_votes' = Ins(elect_votes, h.term, h.vote_logs)
        /\ UNCHANGED commits
        /\ unch_reads

\* t_propose(pre, post, i, cmd): Leader::propose.  cmd ranges over
\* Command \cup {Nil}, standing for Option<Seq<u8>> (A2).
t_propose(i) ==
    \E cmd \in Command \cup {Nil} :
        LET h == hosts[i]
            newlog == Append(h.log, [term |-> h.term, cmd |-> cmd])
        IN  /\ h.role = "Leader"
            /\ Len(h.log) < MaxLog                \* bound, see (A3)
            /\ hosts' = [hosts EXCEPT ![i] = [h EXCEPT !.log = newlog]]
            /\ UNCHANGED net
            /\ leader_log' = Ins(leader_log, h.term, newlog)
            /\ UNCHANGED commits
            /\ unch_elect
            /\ unch_reads

\* t_send_append(pre, post, i, b, e): Leader::maybe_send_append, any window
\* [b, e) of the leader's log.  b, e are prefix lengths, so the window is
\* SubSeq(log, b+1, e).
t_send_append(i) ==
    LET h == hosts[i]
    IN  /\ h.role = "Leader"
        /\ \E b \in 0 .. Len(h.log) : \E e \in 0 .. Len(h.log) :
               /\ b <= e
               /\ LET bt == IF b = 0 THEN 0 ELSE h.log[b].term
                  IN net' = net \cup { MAppend(h.term, b, bt, SubSeq(h.log, b + 1, e)) }
        /\ UNCHANGED hosts
        /\ unch_ghost

\* t_recv_append(pre, post, i, t, b, bt, entries): Message::Append handling +
\* Log::splice.  (t, b, bt, entries) come from the Append message in net (A6).
t_recv_append(i) ==
    \E m \in net :
        /\ m.kind = "Append"
        /\ LET h == hosts[i]
               t  == m.term
               b  == m.base
               bt == m.bterm
               entries == m.entries
               newlog  == splice(h.log, b, entries)
               newvote == IF t > h.term THEN Nil ELSE h.vote
           IN  /\ t >= h.term
               /\ ~(h.role = "Leader" /\ t = h.term)
               \* Rust: `b == 0 || (b <= h.log.len() && h.log[b-1].term == bt)`.
               \* Written with IF/THEN/ELSE rather than `\/`: in next-state
               \* position TLC branches on a disjunction instead of
               \* short-circuiting it, so the `b = 0` guard would not protect
               \* the `h.log[b]` in the other disjunct.
               /\ (IF b = 0 THEN TRUE ELSE (b <= Len(h.log) /\ h.log[b].term = bt))
               /\ hosts' = [hosts EXCEPT ![i] =
                      [h EXCEPT !.term = t, !.vote = newvote,
                                !.role = "Follower", !.log = newlog]]
               /\ net' = net \cup { MAck(i, t, b + Len(entries)) }
               /\ unch_ghost

\* t_send_ack(pre, post, i, mi): a matching HeartbeatResponse, and the leader's
\* own self-match.
t_send_ack(i) ==
    LET h == hosts[i]
    IN  /\ \E mi \in 1 .. Len(h.log) :
               /\ h.log[mi].term = h.term
               /\ net' = net \cup { MAck(i, h.term, mi) }
        /\ UNCHANGED hosts
        /\ unch_ghost

\* t_leader_commit(pre, post, i, ci, q): Leader::maybe_commit_and_apply.
\* q is quantified over [Q -> 0..MaxLog] for a quorum Q (A4).
t_leader_commit(i) ==
    LET h == hosts[i]
    IN  /\ h.role = "Leader"
        /\ \E ci \in 1 .. Len(h.log) :
               /\ h.log[ci].term = h.term            \* section 5.4.2
               /\ \E Q \in SUBSET node_ids :
                      /\ is_quorum(Q)
                      /\ \E q \in [Q -> 0 .. MaxLog] :
                             /\ \A v \in Q : q[v] >= ci /\ MAck(v, h.term, q[v]) \in net
                             /\ LET rec == [term |-> h.term, ci |-> ci, q |-> q]
                                    newcommit == IF ci > h.commit THEN ci ELSE h.commit
                                    newcrec   == IF ci > h.commit THEN rec ELSE h.crec
                                IN /\ hosts' = [hosts EXCEPT ![i] =
                                          [h EXCEPT !.commit = newcommit, !.crec = newcrec]]
                                   /\ net' = net \cup { MCommit(h.term, ci, rec) }
                                   /\ commits' = commits \cup { rec }
        /\ UNCHANGED leader_log
        /\ unch_elect
        /\ unch_reads

\* t_send_commit(pre, post, i, ci): Leader::heartbeat, re-announce a commit.
t_send_commit(i) ==
    LET h == hosts[i]
    IN  /\ h.role = "Leader"
        /\ \E ci \in 1 .. h.commit :
               net' = net \cup { MCommit(h.term, ci, h.crec) }
        /\ UNCHANGED hosts
        /\ unch_ghost

\* t_recv_commit(pre, post, i, ci, mi, rec): Message::Heartbeat commit handling.
\* (ci, rec) come from the Commit message in net (A6); mi is a free parameter.
t_recv_commit(i) ==
    \E m \in net :
        /\ m.kind = "Commit"
        /\ LET h  == hosts[i]
               ci == m.ci
               rec == m.rec
           IN  /\ m.term = h.term
               /\ \E mi \in 1 .. Len(h.log) :
                      /\ ci <= mi
                      /\ h.log[mi].term = h.term
                      /\ LET newcommit == IF ci > h.commit THEN ci ELSE h.commit
                             newcrec   == IF ci > h.commit THEN rec ELSE h.crec
                         IN hosts' = [hosts EXCEPT ![i] =
                                [h EXCEPT !.commit = newcommit, !.crec = newcrec]]
               /\ UNCHANGED net
               /\ unch_ghost

\* t_bump_term(pre, post, i, t): into_follower(term, None) on a higher term,
\* modeled as a spontaneous step.  t is bounded by MaxTerm (A3).
t_bump_term(i) ==
    LET h == hosts[i]
    IN  /\ \E t \in (h.term + 1) .. MaxTerm :
               hosts' = [hosts EXCEPT ![i] =
                   [h EXCEPT !.term = t, !.vote = Nil, !.role = "Follower"]]
        /\ UNCHANGED net
        /\ unch_ghost

\* t_step_down(pre, post, i): Candidate::into_follower in its own term.
t_step_down(i) ==
    LET h == hosts[i]
    IN  /\ h.role = "Candidate"
        /\ hosts' = [hosts EXCEPT ![i] = [h EXCEPT !.role = "Follower"]]
        /\ UNCHANGED net
        /\ unch_ghost

\* t_restart(pre, post, i, c): Node::new after a crash-restart.  Durable state
\* survives; the un-fsynced commit index may regress to any c <= h.commit.
t_restart(i) ==
    LET h == hosts[i]
    IN  /\ \E c \in 0 .. h.commit :
               hosts' = [hosts EXCEPT ![i] =
                   [h EXCEPT !.role = "Follower", !.commit = c, !.votes = {},
                             !.vote_logs = EmptyFn, !.read_seq = 0]]
        /\ UNCHANGED net
        /\ unch_ghost

\* t_submit_read(pre, post, i): ClientRequest::Read handling on the leader.
t_submit_read(i) ==
    LET h == hosts[i]
        s == h.read_seq + 1
    IN  /\ h.role = "Leader"
        /\ h.read_seq < MaxRead                   \* bound, see (A3)
        /\ hosts' = [hosts EXCEPT ![i] = [h EXCEPT !.read_seq = s]]
        /\ net' = net \cup { MRead(h.term, s), MReadConfirm(i, h.term, s) }
        /\ UNCHANGED leader_log
        /\ UNCHANGED commits
        /\ unch_elect
        /\ reads' = reads \cup { [term |-> h.term, seq |-> s, born |-> commits] }
        /\ read_hwm' = Ins(read_hwm, h.term, s)

\* t_confirm_read(pre, post, i, t, s): Message::Read handling.  (t, s) come
\* from the Read message in net (A6).
t_confirm_read(i) ==
    \E m \in net :
        /\ m.kind = "Read"
        /\ LET h == hosts[i]
               t == m.term
               s == m.seq
               newvote == IF t > h.term THEN Nil ELSE h.vote
           IN  /\ t >= h.term
               /\ ~(h.role = "Leader" /\ t = h.term)
               /\ hosts' = [hosts EXCEPT ![i] =
                      [h EXCEPT !.term = t, !.vote = newvote, !.role = "Follower"]]
               /\ net' = net \cup { MReadConfirm(i, t, s) }
               /\ unch_ghost

\* ---------------------------------------------------------------------------
\* Init / Next  (safety.rs `init_host`, `init`, `next_step`, `next`)
\* ---------------------------------------------------------------------------

init_host ==
    [ term |-> 0, vote |-> Nil, role |-> "Follower", log |-> << >>, commit |-> 0,
      votes |-> {}, vote_logs |-> EmptyFn,
      crec |-> [term |-> 0, ci |-> 0, q |-> EmptyFn], read_seq |-> 0 ]

Init ==
    /\ hosts       = [i \in node_ids |-> init_host]
    /\ net         = {}
    /\ leader_log  = EmptyFn
    /\ leader_of   = EmptyFn
    /\ voters      = EmptyFn
    /\ elect_log   = EmptyFn
    /\ elect_votes = EmptyFn
    /\ commits     = {}
    /\ reads       = {}
    /\ read_hwm    = EmptyFn

\* next(pre, post) == exists a TStep.  One disjunct per TStep variant, in the
\* order of the TStep enum; the step's node parameter is the outer \E.
Next ==
    \/ \E i \in node_ids : t_campaign(i)
    \/ \E v \in node_ids : t_grant(v)
    \/ \E i \in node_ids : t_collect_vote(i)
    \/ \E i \in node_ids : t_become_leader(i)
    \/ \E i \in node_ids : t_propose(i)
    \/ \E i \in node_ids : t_send_append(i)
    \/ \E i \in node_ids : t_recv_append(i)
    \/ \E i \in node_ids : t_send_ack(i)
    \/ \E i \in node_ids : t_leader_commit(i)
    \/ \E i \in node_ids : t_send_commit(i)
    \/ \E i \in node_ids : t_recv_commit(i)
    \/ \E i \in node_ids : t_bump_term(i)
    \/ \E i \in node_ids : t_step_down(i)
    \/ \E i \in node_ids : t_restart(i)
    \/ \E i \in node_ids : t_submit_read(i)
    \/ \E i \in node_ids : t_confirm_read(i)

Spec == Init /\ [][Next]_vars

\* ---------------------------------------------------------------------------
\* Types.  There is no TypeOK in safety.rs (Verus types the state
\* structurally); this is the TLA+ stand-in, and the domains are what the
\* tlc_cti probe has to enumerate.
\* ---------------------------------------------------------------------------

Role  == { "Follower", "Candidate", "Leader" }
Term  == 0 .. MaxTerm
Entry == [term : 1 .. MaxTerm, cmd : Command \cup {Nil}]

\* Bounded sequences over S, lengths 0..k.  These declarative domains are
\* what the CTI probe (Raft_cti.tla) would have to enumerate; TypeOK below
\* states the same thing structurally, which is what TLC can afford to
\* evaluate on every state (a membership test in `[V -> Logs]` enumerates up
\* to |Logs|^|V| functions, which dominated the run).
BSeq(S, k) == UNION { [1 .. j -> S] : j \in 0 .. k }

Logs == BSeq(Entry, MaxLog)

CommitRecs == [term : Term, ci : 0 .. MaxLog,
               q : UNION { [Q -> 0 .. MaxLog] : Q \in SUBSET node_ids }]

Messages ==
       [kind : {"Campaign"},    c : node_ids, term : 1 .. MaxTerm, clog : Logs]
  \cup [kind : {"Vote"},        v : node_ids, c : node_ids, term : 1 .. MaxTerm, vlog : Logs]
  \cup [kind : {"Append"},      term : 1 .. MaxTerm, base : 0 .. MaxLog,
                                bterm : Term, entries : Logs]
  \cup [kind : {"Commit"},      term : 1 .. MaxTerm, ci : 0 .. MaxLog, rec : CommitRecs]
  \cup [kind : {"Ack"},         v : node_ids, term : 1 .. MaxTerm, mi : 0 .. MaxLog]
  \cup [kind : {"Read"},        term : 1 .. MaxTerm, seq : 1 .. MaxRead]
  \cup [kind : {"ReadConfirm"}, v : node_ids, term : 1 .. MaxTerm, seq : 1 .. MaxRead]

MHosts ==
    [ term : Term, vote : node_ids \cup {Nil}, role : Role, log : Logs,
      commit : 0 .. MaxLog, votes : SUBSET node_ids,
      vote_logs : UNION { [V -> Logs] : V \in SUBSET node_ids },
      crec : CommitRecs, read_seq : 0 .. MaxRead ]

ReadRecs == [term : Term, seq : 1 .. MaxRead, born : SUBSET CommitRecs]

\* The structural equivalents, used by TypeOK.
is_log(l)  == l \in Seq(Entry) /\ Len(l) <= MaxLog
is_qfn(q)  == DOMAIN q \subseteq node_ids /\ \A v \in DOMAIN q : q[v] \in 0 .. MaxLog
is_crec(r) == DOMAIN r = {"term", "ci", "q"}
              /\ r.term \in Term /\ r.ci \in 0 .. MaxLog /\ is_qfn(r.q)
is_logfn(f, D) == DOMAIN f \subseteq D /\ \A x \in DOMAIN f : is_log(f[x])

is_msg(m) ==
    CASE m.kind = "Campaign" -> DOMAIN m = {"kind", "c", "term", "clog"}
                                /\ m.c \in node_ids /\ m.term \in 1 .. MaxTerm
                                /\ is_log(m.clog)
      [] m.kind = "Vote"     -> DOMAIN m = {"kind", "v", "c", "term", "vlog"}
                                /\ m.v \in node_ids /\ m.c \in node_ids
                                /\ m.term \in 1 .. MaxTerm /\ is_log(m.vlog)
      [] m.kind = "Append"   -> DOMAIN m = {"kind", "term", "base", "bterm", "entries"}
                                /\ m.term \in 1 .. MaxTerm /\ m.base \in 0 .. MaxLog
                                /\ m.bterm \in Term /\ is_log(m.entries)
      [] m.kind = "Commit"   -> DOMAIN m = {"kind", "term", "ci", "rec"}
                                /\ m.term \in 1 .. MaxTerm /\ m.ci \in 0 .. MaxLog
                                /\ is_crec(m.rec)
      [] m.kind = "Ack"      -> DOMAIN m = {"kind", "v", "term", "mi"}
                                /\ m.v \in node_ids /\ m.term \in 1 .. MaxTerm
                                /\ m.mi \in 0 .. MaxLog
      [] m.kind = "Read"     -> DOMAIN m = {"kind", "term", "seq"}
                                /\ m.term \in 1 .. MaxTerm /\ m.seq \in 1 .. MaxRead
      [] m.kind = "ReadConfirm" -> DOMAIN m = {"kind", "v", "term", "seq"}
                                /\ m.v \in node_ids /\ m.term \in 1 .. MaxTerm
                                /\ m.seq \in 1 .. MaxRead
      [] OTHER -> FALSE

is_host(h) ==
    /\ DOMAIN h = {"term", "vote", "role", "log", "commit", "votes",
                   "vote_logs", "crec", "read_seq"}
    /\ h.term \in Term
    /\ (h.vote = Nil \/ h.vote \in node_ids)
    /\ h.role \in Role
    /\ is_log(h.log)
    /\ h.commit \in 0 .. MaxLog
    /\ h.votes \subseteq node_ids
    /\ is_logfn(h.vote_logs, node_ids)
    /\ is_crec(h.crec)
    /\ h.read_seq \in 0 .. MaxRead

is_rrec(r) ==
    /\ DOMAIN r = {"term", "seq", "born"}
    /\ r.term \in Term
    /\ r.seq \in 1 .. MaxRead
    /\ \A rec \in r.born : is_crec(rec)

TypeOK ==
    /\ DOMAIN hosts = node_ids
    /\ \A i \in node_ids : is_host(hosts[i])
    /\ \A m \in net : is_msg(m)
    /\ is_logfn(leader_log, 1 .. MaxTerm)
    /\ DOMAIN leader_of \subseteq 1 .. MaxTerm
    /\ \A t \in DOMAIN leader_of : leader_of[t] \in node_ids
    /\ DOMAIN voters \subseteq 1 .. MaxTerm
    /\ \A t \in DOMAIN voters : voters[t] \subseteq node_ids
    /\ is_logfn(elect_log, 1 .. MaxTerm)
    /\ DOMAIN elect_votes \subseteq 1 .. MaxTerm
    /\ \A t \in DOMAIN elect_votes : is_logfn(elect_votes[t], node_ids)
    /\ \A rec \in commits : is_crec(rec)
    /\ \A r \in reads : is_rrec(r)
    /\ DOMAIN read_hwm \subseteq 1 .. MaxTerm
    /\ \A t \in DOMAIN read_hwm : read_hwm[t] \in 1 .. MaxRead

\* ---------------------------------------------------------------------------
\* Invariants: structural well-formedness
\* ---------------------------------------------------------------------------

\* inv_wf(s)
inv_wf ==
    /\ N >= 1
    /\ DOMAIN hosts = node_ids

\* ---------------------------------------------------------------------------
\* Invariants: per-host state
\* ---------------------------------------------------------------------------

\* host_ok(s, i)
host_ok(i) ==
    LET h == hosts[i]
    IN  /\ log_wf(h.log)
        /\ terms_le(h.log, h.term)
        /\ log_pinned(leader_log, h.log)
        /\ h.votes \subseteq node_ids
        /\ (h.vote # Nil => h.vote \in node_ids)
        \* Candidates.
        /\ (h.role = "Candidate" =>
              /\ h.term >= 1
              /\ h.vote = i
              /\ MCampaign(i, h.term, h.log) \in net
              /\ terms_lt(h.log, h.term)
              /\ \A v \in h.votes :
                     /\ v \in DOMAIN h.vote_logs
                     /\ MVote(v, i, h.term, h.vote_logs[v]) \in net
              /\ (h.term \in DOMAIN leader_of => leader_of[h.term] # i))
        \* Leaders.
        /\ (h.role = "Leader" =>
              /\ h.term >= 1
              /\ h.vote = i
              /\ h.term \in DOMAIN leader_log
              /\ LOf(h.term) = i
              /\ leader_log[h.term] = h.log
              /\ (h.term \in DOMAIN read_hwm => read_hwm[h.term] = h.read_seq)
              /\ (h.term \notin DOMAIN read_hwm => h.read_seq = 0))

inv_hosts == \A i \in node_ids : host_ok(i)

\* ---------------------------------------------------------------------------
\* Invariants: messages
\* ---------------------------------------------------------------------------

\* campaign_msg_ok(s, c, t, clog)
campaign_msg_ok(c, t, clog) ==
    /\ c \in node_ids
    /\ t >= 1
    /\ hosts[c].term >= t
    /\ log_wf(clog)
    /\ terms_lt(clog, t)
    /\ log_pinned(leader_log, clog)

\* vote_msg_ok(s, v, c, t, vlog)
vote_msg_ok(v, c, t, vlog) ==
    /\ v \in node_ids
    /\ c \in node_ids
    /\ t >= 1
    /\ hosts[v].term >= t
    /\ (hosts[v].term = t => hosts[v].vote = c)
    /\ hosts[c].term >= t
    /\ log_wf(vlog)
    /\ terms_le(vlog, t)
    /\ log_pinned(leader_log, vlog)
    /\ ((hosts[c].role = "Candidate" /\ hosts[c].term = t) => up_to_date(hosts[c].log, vlog))

\* append_msg_ok(s, t, b, bt, entries)
append_msg_ok(t, b, bt, entries) ==
    /\ t >= 1
    /\ t \in DOMAIN leader_log
    /\ b + Len(entries) <= Len(leader_log[t])
    /\ \A j \in 1 .. Len(entries) : entries[j] = leader_log[t][b + j]
    /\ (b >= 1 => (b <= Len(leader_log[t]) /\ bt = leader_log[t][b].term))
    /\ (b = 0 => bt = 0)

\* ack_msg_ok(s, v, t, mi)
ack_msg_ok(v, t, mi) ==
    /\ v \in node_ids
    /\ t >= 1
    /\ hosts[v].term >= t
    /\ t \in DOMAIN leader_log
    /\ mi <= Len(leader_log[t])
    /\ (hosts[v].term = t => prefix_eq(hosts[v].log, leader_log[t], mi))

inv_msgs ==
    /\ \A m \in net : m.kind = "Campaign" => campaign_msg_ok(m.c, m.term, m.clog)
    \* A node campaigns at most once per term.
    /\ \A m1 \in net : \A m2 \in net :
           (m1.kind = "Campaign" /\ m2.kind = "Campaign"
            /\ m1.c = m2.c /\ m1.term = m2.term) => m1.clog = m2.clog
    /\ \A m \in net : m.kind = "Vote" => vote_msg_ok(m.v, m.c, m.term, m.vlog)
    \* Vote once per term.
    /\ \A m1 \in net : \A m2 \in net :
           (m1.kind = "Vote" /\ m2.kind = "Vote"
            /\ m1.v = m2.v /\ m1.term = m2.term) => m1.c = m2.c
    /\ \A m \in net : m.kind = "Append" => append_msg_ok(m.term, m.base, m.bterm, m.entries)
    /\ \A m \in net : m.kind = "Ack" => ack_msg_ok(m.v, m.term, m.mi)

\* ---------------------------------------------------------------------------
\* Invariants: per-term leader logs and election evidence
\* ---------------------------------------------------------------------------

\* frozen_persist_at(s, u, vlog, t, mi)
frozen_persist_at(u, vlog, t, mi) ==
    \A i \in 0 .. mi : mid_compliant(leader_log, t, u, i) => prefix_eq(vlog, LL(t), i)

\* frozen_persist_ok(s, u, vlog, w)
frozen_persist_ok(u, vlog, w) ==
    \A m \in net :
        (m.kind = "Ack" /\ m.v = w /\ m.term < u) => frozen_persist_at(u, vlog, m.term, m.mi)

\* voter_ok(s, u, x).  The Rust binds `vlog = s.elect_votes[u][x]` in a `let`
\* above the domain check; TLA+ function application is not total, so the
\* domain check is hoisted above the LET.  Same meaning (A5).
voter_ok(u, x) ==
    /\ x \in DOMAIN elect_votes[u]
    /\ LET vlog == elect_votes[u][x]
       IN  /\ MVote(x, LOf(u), u, vlog) \in net
           /\ up_to_date(elect_log[u], vlog)
           /\ frozen_persist_ok(u, vlog, x)

\* lterm_ok(s, u).  `elog = s.elect_log[u]` likewise hoisted below the domain
\* conjunct it depends on.
lterm_ok(u) ==
    LET ll == leader_log[u]
    IN  /\ u >= 1
        /\ Len(ll) >= 1
        /\ log_wf(ll)
        /\ terms_le(ll, u)
        /\ log_pinned(leader_log, ll)
        /\ last_term(ll) = u
        /\ LOf(u) \in node_ids
        /\ hosts[LOf(u)].term >= u
        /\ u \in DOMAIN voters
        /\ u \in DOMAIN elect_log
        /\ u \in DOMAIN elect_votes
        /\ is_quorum(voters[u])
        /\ LET elog == elect_log[u]
           IN  /\ prefix_eq(ll, elog, Len(elog))
               /\ Len(elog) < Len(ll)
               /\ ll[Len(elog) + 1].term = u
               /\ terms_lt(elog, u)
               /\ log_wf(elog)
        /\ \A x \in voters[u] : voter_ok(u, x)

inv_lterms ==
    /\ DOMAIN leader_of = DOMAIN leader_log
    /\ DOMAIN read_hwm \subseteq DOMAIN leader_log
    /\ \A u \in DOMAIN leader_log : lterm_ok(u)

\* ---------------------------------------------------------------------------
\* Invariants: acked-prefix persistence
\* ---------------------------------------------------------------------------

\* ack_persist_ok(s, v, t, mi)  (K2c)
ack_persist_ok(v, t, mi) ==
    \A i \in 0 .. mi :
        mid_compliant(leader_log, t, hosts[v].term + 1, i)
            => prefix_eq(hosts[v].log, LL(t), i)

inv_ack_persist ==
    \A m \in net : m.kind = "Ack" => ack_persist_ok(m.v, m.term, m.mi)

\* vote_persist_ok(s, u, vlog, t, mi)  (K3'')
vote_persist_ok(u, vlog, t, mi) ==
    \A i \in 0 .. mi :
        mid_compliant(leader_log, t, u + 1, i) => prefix_eq(vlog, LL(t), i)

inv_vote_persist ==
    \A mv \in net : \A ma \in net :
        (mv.kind = "Vote" /\ ma.kind = "Ack" /\ ma.v = mv.v /\ ma.term < mv.term)
            => vote_persist_ok(mv.term, mv.vlog, ma.term, ma.mi)

\* ---------------------------------------------------------------------------
\* Invariants: commits and leader completeness
\* ---------------------------------------------------------------------------

\* commit_rec_ok(s, rec)  (CM1)
commit_rec_ok(rec) ==
    /\ rec.term \in DOMAIN leader_log
    /\ 1 <= rec.ci /\ rec.ci <= Len(leader_log[rec.term])
    /\ leader_log[rec.term][rec.ci].term = rec.term
    /\ is_quorum(DOMAIN rec.q)
    /\ \A v \in DOMAIN rec.q :
           rec.q[v] >= rec.ci /\ MAck(v, rec.term, rec.q[v]) \in net

inv_commits == \A rec \in commits : commit_rec_ok(rec)

\* inv_leader_completeness(s)  (D)
inv_leader_completeness ==
    \A rec \in commits : \A u \in DOMAIN leader_log :
        u > rec.term => prefix_eq(leader_log[u], LL(rec.term), rec.ci)

\* commit_msg_ok(s, t, ci, rec)
commit_msg_ok(t, ci, rec) ==
    /\ t >= 1
    /\ ci >= 1
    /\ t \in DOMAIN leader_log
    /\ ci <= Len(leader_log[t])
    /\ rec \in commits
    /\ rec.ci >= ci
    /\ rec.term <= t
    /\ prefix_eq(leader_log[t], LL(rec.term), ci)

inv_commit_msgs ==
    \A m \in net : m.kind = "Commit" => commit_msg_ok(m.term, m.ci, m.rec)

\* host_commit_ok(s, i)  (HC)
host_commit_ok(i) ==
    LET h == hosts[i]
    IN  h.commit > 0 =>
        /\ h.crec \in commits
        /\ h.crec.ci >= h.commit
        /\ h.crec.term <= h.term
        /\ prefix_eq(h.log, LL(h.crec.term), h.commit)

inv_host_commits == \A i \in node_ids : host_commit_ok(i)

\* commit_leader_ok(s, rec)
commit_leader_ok(rec) ==
    LET l == hosts[LOf(rec.term)]
    IN  (l.role = "Leader" /\ l.term = rec.term) => l.commit >= rec.ci

inv_commit_leaders == \A rec \in commits : commit_leader_ok(rec)

\* ---------------------------------------------------------------------------
\* Invariants: linearizable reads
\* ---------------------------------------------------------------------------

\* read_msg_ok(s, t, sq)
read_msg_ok(t, sq) ==
    /\ t \in DOMAIN read_hwm
    /\ 1 <= sq /\ sq <= read_hwm[t]

\* confirm_msg_ok(s, v, t, sq)
confirm_msg_ok(v, t, sq) ==
    /\ v \in node_ids
    /\ hosts[v].term >= t
    /\ t \in DOMAIN read_hwm
    /\ 1 <= sq /\ sq <= read_hwm[t]

\* read_rec_ok(s, r)  (R2, the linearizability core)
read_rec_ok(r) ==
    /\ 1 <= r.seq
    /\ r.term \in DOMAIN read_hwm
    /\ r.seq <= read_hwm[r.term]
    /\ \A rec \in r.born : rec \in commits
    /\ \A rec \in r.born : \A z \in DOMAIN rec.q : \A m \in net :
           (rec.term > r.term /\ m.kind = "ReadConfirm" /\ m.v = z /\ m.term = r.term)
               => m.seq < r.seq

inv_reads ==
    /\ \A m \in net : m.kind = "Read" => read_msg_ok(m.term, m.seq)
    /\ \A m \in net : m.kind = "ReadConfirm" => confirm_msg_ok(m.v, m.term, m.seq)
    /\ \A r \in reads : read_rec_ok(r)

\* ---------------------------------------------------------------------------
\* inv(s)
\* ---------------------------------------------------------------------------

Inv ==
    /\ inv_wf
    /\ inv_hosts
    /\ inv_msgs
    /\ inv_lterms
    /\ inv_ack_persist
    /\ inv_vote_persist
    /\ inv_commits
    /\ inv_leader_completeness
    /\ inv_commit_msgs
    /\ inv_host_commits
    /\ inv_commit_leaders
    /\ inv_reads

\* ---------------------------------------------------------------------------
\* Vacuity witnesses.  Not part of safety.rs.  Each is the negation of the
\* antecedent of a conjunct that is easy to satisfy vacuously; a run that
\* *violates* the witness proves the antecedent is reachable, so the conjunct
\* was checked non-vacuously at those bounds.  At Raft.cfg's bounds both
\* hold on every reachable state (both conjuncts are vacuous there); the
\* Raft_deep_*_witness.cfg runs violate them.
\* ---------------------------------------------------------------------------

\* inv_leader_completeness's antecedent: a commit and a strictly later
\* elected term.
NoLC == ~(\E rec \in commits : \E u \in DOMAIN leader_log : u > rec.term)

\* read_rec_ok's R2 antecedent: a read record whose born set holds a commit
\* of a higher term than the read's own.
NoR2 == ~(\E r \in reads : \E rec \in r.born : rec.term > r.term)

\* ---------------------------------------------------------------------------
\* The bounding state constraint.  Terms, log lengths and read sequence
\* numbers are what grow without bound in the model.  Message payloads are
\* copies of host / leader logs, so bounding those bounds the network too.
\* ---------------------------------------------------------------------------

Constraint ==
    /\ \A i \in node_ids :
           /\ hosts[i].term <= MaxTerm
           /\ Len(hosts[i].log) <= MaxLog
           /\ hosts[i].read_seq <= MaxRead
    /\ \A t \in DOMAIN leader_log : Len(leader_log[t]) <= MaxLog
    /\ Cardinality(net) <= MaxMsgs

=============================================================================
