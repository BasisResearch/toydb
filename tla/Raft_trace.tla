----------------------------- MODULE Raft_trace -----------------------------
(***************************************************************************)
(* Trace validation of toyDB's Raft shell against Raft.tla.               *)
(*                                                                         *)
(* The node tests, built with `--features tla-trace`, log every model step *)
(* the shell takes through a verified step function (`src/raft/node.rs`,   *)
(* `trace_step!`), one JSON line each: the `t_*` transition, its           *)
(* parameters, and the stepping node's observed host state afterwards, in  *)
(* the Verus exporter's value encoding (see `tla-trace/`).  This module    *)
(* follows such a log: TraceNext takes the logged step, one of Next's     *)
(* disjuncts (so it only narrows the model), and compares the observed    *)
(* fields.  TLC                                                            *)
(* exploring it explores the behaviours of Raft that explain the log; the  *)
(* log conforms when some state reaches TraceAccepted, and otherwise the   *)
(* deepest trace_i is the first step no such behaviour can take.           *)
(*                                                                         *)
(* It is the hand-written counterpart of the trace spec `verus -V          *)
(* tla-export` writes beside an export, with the same interface            *)
(* (TraceLog, one VARIABLE, TraceInit, TraceNext, TraceEnabled,            *)
(* TraceDiagnosis, TraceStepAt), so verus-tools-mcp's tlc_conform runs     *)
(* either.  What differs is the value mapping, which Raft.tla's own        *)
(* approximations dictate:                                                 *)
(*                                                                         *)
(*  - a vote is a rank or Nil (the log's `{"tag": "None"}`);              *)
(*  - a role is a string (the log's `{"tag": "Leader"}`);                  *)
(*  - an entry's command is Nil for the noop and some element of Command  *)
(*    otherwise (A2): the log says only which; run with Command = {c1}    *)
(*    so every write is the same abstract command;                         *)
(*  - hosts is a function on 0..N-1, observed by rank ("0", "1", ...).    *)
(*                                                                         *)
(* Raft.tla's actions take the node as their only parameter and bind the  *)
(* rest from the network (A6); the logged parameters that the network or  *)
(* the post state determine pin those bindings below (TraceStep).  Each    *)
(* arm of TraceStep is `t_x(i)` for a node i, a disjunct of Next, so       *)
(* unlike the exporter's trace spec this one does not conjoin Next again:  *)
(* evaluating all of Next at every step makes TLC enumerate               *)
(* t_leader_commit's ack maps [Q -> 0..MaxLog], which is past a million   *)
(* functions at N = 5.  For the same reason t_leader_commit is taken at    *)
(* its logged witness (Q, q) (LeaderCommitAt), which is t_leader_commit's *)
(* body with its existentials instantiated.                                *)
(*                                                                         *)
(* Run with CONSTANT TraceLog = "<log>", N the logged cluster size, and    *)
(* MaxTerm, MaxLog, MaxRead above anything the log reaches (they are      *)
(* guards in Raft.tla, A3).                                                *)
(***************************************************************************)
EXTENDS Raft, Json, TLC, Integers, Sequences, FiniteSets

CONSTANT TraceLog  \* the log's path

VARIABLE trace_i   \* the next logged step to take

TraceLines == ndJsonDeserialize(TraceLog)
TraceHeader == TraceLines[1]
Trace == SubSeq(TraceLines, 2, Len(TraceLines))

\* Whether a JSON value is an array (TLC holds it as a tuple).
TraceIsArray(j) == SubSeq(ToString(j), 1, 2) = "<<"
TraceStateOf(e) == IF "state" \in DOMAIN e THEN e.state ELSE [k \in {} |-> 0]

\* ---------------------------------------------------------------------------
\* Observations, in the exporter's encoding.  An object is partial: only the
\* fields it names are compared.
\* ---------------------------------------------------------------------------

DecVote(j) == IF j.tag = "None" THEN Nil ELSE j.v0

ObsEntry(en, j) ==
    \A k \in DOMAIN j :
        CASE k = "term" -> en.term = j.term
          [] k = "cmd"  -> IF j.cmd.tag = "None" THEN en.cmd = Nil ELSE en.cmd \in Command
          [] OTHER      -> Assert(FALSE, "trace: an entry has no field " \o k)

\* A whole log (an array), or some entries of it keyed by Verus index.
ObsLog(l, j) ==
    IF TraceIsArray(j)
    THEN Len(l) = Len(j) /\ \A p \in 1 .. Len(j) : ObsEntry(l[p], j[p])
    ELSE \A k \in DOMAIN j : \E p \in 1 .. Len(l) : ToString(p - 1) = k /\ ObsEntry(l[p], j[k])

ObsHost(h, j) ==
    \A k \in DOMAIN j :
        CASE k = "term"     -> h.term = j.term
          [] k = "vote"     -> h.vote = DecVote(j.vote)
          [] k = "role"     -> h.role = j.role.tag
          [] k = "log"      -> ObsLog(h.log, j.log)
          [] k = "commit"   -> h.commit = j.commit
          [] k = "votes"    -> h.votes = {j.votes[p] : p \in 1 .. Len(j.votes)}
          [] k = "read_seq" -> h.read_seq = j.read_seq
          [] OTHER          -> Assert(FALSE, "trace: MHost has no field " \o k)

ObsHosts(hs, j) ==
    \A r \in DOMAIN j : \E n \in node_ids : ToString(n) = r /\ ObsHost(hs[n], j[r])

TraceObservedKey(k, j) ==
    CASE k = "hosts" -> ObsHosts(hosts, j)
      [] OTHER       -> Assert(FALSE, "trace: only hosts is observed, not " \o k)
TraceObserved(j) == \A k \in DOMAIN j : TraceObservedKey(k, j[k])

\* The same of the next state: its variables primed, never the log's index.
TraceObservedKeyNext(k, j) ==
    CASE k = "hosts" -> ObsHosts(hosts', j)
      [] OTHER       -> Assert(FALSE, "trace: only hosts is observed, not " \o k)
TraceObservedNext(j) == \A k \in DOMAIN j : TraceObservedKeyNext(k, j[k])

\* ---------------------------------------------------------------------------
\* The logged step: Raft.tla's action for the node, the other logged
\* parameters pinning what it binds from the network.
\* ---------------------------------------------------------------------------

\* A Map<int, nat> logged as [key, value] pairs.
DecMap(j) == [k \in {j[p][1] : p \in 1 .. Len(j)} |-> j[CHOOSE p \in 1 .. Len(j) : j[p][1] = k][2]]

\* t_leader_commit(i) at the witness ci, Q = DOMAIN q, q: its body, with
\* the three existentials instantiated (so it implies t_leader_commit(i)).
LeaderCommitAt(i, ci, q) ==
    LET h == hosts[i]
        Q == DOMAIN q
    IN  /\ h.role = "Leader"
        /\ ci \in 1 .. Len(h.log)
        /\ h.log[ci].term = h.term
        /\ Q \subseteq node_ids
        /\ is_quorum(Q)
        /\ \A v \in Q : q[v] \in 0 .. MaxLog
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

TraceStep(e) ==
    LET P(k) == e.params[k]
        i    == IF e.step = "t_grant" THEN P("v") ELSE P("i")
        h    == hosts[i]
    IN
    /\ i \in node_ids
    /\ CASE e.step = "t_campaign"      -> t_campaign(i)
      [] e.step = "t_grant"         -> /\ t_grant(i)
                                       /\ hosts'[i].vote = P("c")
                                       /\ hosts'[i].term = P("term")
      [] e.step = "t_collect_vote"  -> /\ t_collect_vote(i)
                                       /\ hosts'[i].votes = h.votes \cup {P("v")}
                                       /\ P("v") \in DOMAIN hosts'[i].vote_logs
      [] e.step = "t_become_leader" -> t_become_leader(i)
      [] e.step = "t_propose"       -> t_propose(i)
      [] e.step = "t_send_append"   -> /\ t_send_append(i)
                                       /\ net' = net \cup
                                            { MAppend(h.term, P("b"),
                                                      IF P("b") = 0 THEN 0 ELSE h.log[P("b")].term,
                                                      SubSeq(h.log, P("b") + 1, P("e"))) }
      [] e.step = "t_recv_append"   -> t_recv_append(i) /\ hosts'[i].term = P("term")
      [] e.step = "t_send_ack"      -> /\ t_send_ack(i)
                                       /\ net' = net \cup {MAck(i, h.term, P("mi"))}
      [] e.step = "t_leader_commit" -> LeaderCommitAt(i, P("ci"), DecMap(P("q")))
      [] e.step = "t_send_commit"   -> /\ t_send_commit(i)
                                       /\ net' = net \cup {MCommit(h.term, P("ci"), h.crec)}
      [] e.step = "t_recv_commit"   -> /\ t_recv_commit(i)
                                       /\ \E m \in net : m.kind = "Commit" /\ m.term = h.term
                                                         /\ m.ci = P("ci")
      [] e.step = "t_bump_term"     -> t_bump_term(i) /\ hosts'[i].term = P("term")
      [] e.step = "t_step_down"     -> t_step_down(i)
      [] e.step = "t_restart"       -> t_restart(i) /\ hosts'[i].commit = P("commit")
      [] e.step = "t_submit_read"   -> t_submit_read(i)
      [] e.step = "t_confirm_read"  -> /\ t_confirm_read(i)
                                       /\ net' = net \cup {MReadConfirm(i, P("term"), P("seq"))}
      [] OTHER -> Assert(FALSE, "trace: Raft has no step " \o e.step)

TraceInit ==
    /\ Init
    /\ trace_i = 1
    /\ TraceObserved(TraceStateOf(TraceHeader))

TraceNext ==
    /\ trace_i <= Len(Trace)
    /\ LET e == Trace[trace_i] IN
           /\ TraceStep(e)
           /\ TraceObservedNext(TraceStateOf(e))
    /\ trace_i' = trace_i + 1

TraceSpec == TraceInit /\ [][TraceNext]_<<vars, trace_i>>

\* The whole log was followed.
TraceAccepted == trace_i = Len(Trace) + 1

TraceStepAt == Trace[trace_i]

\* ---------------------------------------------------------------------------
\* At a divergence
\* ---------------------------------------------------------------------------

StepNames == {"t_campaign", "t_grant", "t_collect_vote", "t_become_leader", "t_propose",
              "t_send_append", "t_recv_append", "t_send_ack", "t_leader_commit",
              "t_send_commit", "t_recv_commit", "t_bump_term", "t_step_down", "t_restart",
              "t_submit_read", "t_confirm_read"}

\* ENABLED t_leader_commit(n), without enumerating its ack maps: each q[v]
\* is chosen on its own, so a quorum each of whose members has an ack of
\* the term at or past ci (and within MaxLog) is exactly an enabling one.
LeaderCommitEnabled(n) ==
    LET h == hosts[n]
    IN  /\ h.role = "Leader"
        /\ \E ci \in 1 .. Len(h.log) :
               /\ h.log[ci].term = h.term
               /\ \E Q \in SUBSET node_ids :
                      /\ is_quorum(Q)
                      /\ \A v \in Q : \E m \in net :
                             /\ m.kind = "Ack" /\ m.v = v /\ m.term = h.term
                             /\ m.mi >= ci /\ m.mi <= MaxLog

Act(a, n) ==
    CASE a = "t_campaign"      -> t_campaign(n)
      [] a = "t_grant"         -> t_grant(n)
      [] a = "t_collect_vote"  -> t_collect_vote(n)
      [] a = "t_become_leader" -> t_become_leader(n)
      [] a = "t_propose"       -> t_propose(n)
      [] a = "t_send_append"   -> t_send_append(n)
      [] a = "t_recv_append"   -> t_recv_append(n)
      [] a = "t_send_ack"      -> t_send_ack(n)
      [] a = "t_leader_commit" -> LeaderCommitEnabled(n)
      [] a = "t_send_commit"   -> t_send_commit(n)
      [] a = "t_recv_commit"   -> t_recv_commit(n)
      [] a = "t_bump_term"     -> t_bump_term(n)
      [] a = "t_step_down"     -> t_step_down(n)
      [] a = "t_restart"       -> t_restart(n)
      [] a = "t_submit_read"   -> t_submit_read(n)
      [] a = "t_confirm_read"  -> t_confirm_read(n)

\* The model's steps enabled in the current state, each for its node (the
\* rest of its parameters are bound from the network, A6). Act is the action,
\* but for t_leader_commit its enabledness (LeaderCommitEnabled).
TraceEnabled ==
    {[step |-> an[1], params |-> [i |-> an[2]]] :
        an \in {an \in StepNames \X node_ids : ENABLED Act(an[1], an[2])}}

\* Whether the log's next step is enabled at all, and which observed fields
\* no successor by it matches.
TraceDiagnosis ==
    LET e == TraceStepAt IN
    [ step_enabled |-> ENABLED TraceStep(e),
      unmatched |-> {k \in DOMAIN TraceStateOf(e) :
                        ~ENABLED (TraceStep(e) /\ TraceObservedKeyNext(k, TraceStateOf(e)[k]))} ]
=============================================================================
