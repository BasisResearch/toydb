------------------------------ MODULE Raft_cti ------------------------------
(***************************************************************************)
(* The inductiveness probe of `tlc_cti`, written by hand: replace INIT by  *)
(* `TypeOK /\ Inv`, take one step, and check every `inv_*` conjunct on the *)
(* successor.  A counterexample-to-induction found here may be             *)
(* unreachable; it is a proof hint about Verus's `step_preserves_inv`,     *)
(* never a bug report about the protocol.                                  *)
(*                                                                         *)
(* Use Raft_cti.cfg (the probe as specified) or Raft_cti_small.cfg (the    *)
(* tightened seed, see CtiSeed below).                                     *)
(***************************************************************************)
EXTENDS Raft, TLC

\* Raft's TypeOK is written structurally (DOMAIN tests, \A over members) so
\* that TLC can afford it as an invariant.  TLC's initial-state computation
\* needs the enumerable form `var \in Set` instead, so the probe restates it
\* over the declarative domains of Raft.tla.  The two are equivalent.
CtiTypeOK ==
    /\ hosts \in [node_ids -> MHosts]
    /\ net \in SUBSET Messages
    /\ leader_log  \in UNION { [T -> Logs] : T \in SUBSET (1 .. MaxTerm) }
    /\ leader_of   \in UNION { [T -> node_ids] : T \in SUBSET (1 .. MaxTerm) }
    /\ voters      \in UNION { [T -> SUBSET node_ids] : T \in SUBSET (1 .. MaxTerm) }
    /\ elect_log   \in UNION { [T -> Logs] : T \in SUBSET (1 .. MaxTerm) }
    /\ elect_votes \in UNION { [T -> UNION { [V -> Logs] : V \in SUBSET node_ids }]
                                : T \in SUBSET (1 .. MaxTerm) }
    /\ commits \in SUBSET CommitRecs
    /\ reads \in SUBSET ReadRecs
    /\ read_hwm \in UNION { [T -> 1 .. MaxRead] : T \in SUBSET (1 .. MaxTerm) }

\* The probe as tlc_cti would inject it.
CtiInit == CtiTypeOK /\ Inv

\* One step only.
CtiOneStep == TLCGet("level") < 2

\* ---------------------------------------------------------------------------
\* Tightened seed.  `CtiInit` is not enumerable: TLC must construct every
\* assignment satisfying TypeOK, and `net` alone ranges over the powerset of
\* the message universe (about 10^2 messages even at N=2, MaxTerm=1,
\* MaxLog=1, so about 2^100 values), with `hosts` contributing another 10^11.
\* Shrinking N, MaxTerm, MaxLog and Command does not change that: the
\* powersets survive.  What does work is seeding a *small explicit* family
\* of pre-states and letting TLC vary only the dimensions the conjunct under
\* test depends on.
\*
\* CtiSeed is the post-election configuration of a three-node cluster: term 1
\* elected node 0 by the quorum {0,1}, the term-1 leader log is the single
\* noop entry, and node 0's commit record for that entry is in `commits`,
\* acked by {0,1}.  Node 2 is free to be anywhere in 0..MaxTerm with any log
\* of length <= MaxLog, and `net` carries exactly the messages the election
\* and the commit produced.  Every state in the family satisfies TypeOK.
\* ---------------------------------------------------------------------------

NoopEntry(t) == [term |-> t, cmd |-> Nil]
Ent(t, c)    == [term |-> t, cmd |-> c]

L1      == << NoopEntry(1) >>
ZeroRec == [term |-> 0, ci |-> 0, q |-> EmptyFn]
Rec1    == [term |-> 1, ci |-> 1, q |-> [x \in {0, 1} |-> 1]]

\* The messages the term-1 election and the term-1 commit produced.
CtiNet ==
    { MCampaign(0, 1, << >>), MVote(0, 0, 1, << >>), MVote(1, 0, 1, << >>),
      MAck(0, 1, 1), MAck(1, 1, 1), MCommit(1, 1, Rec1) }

\* The messages a term-2 election by node 2 would have produced.
CtiExtra(lg2) ==
    { MCampaign(2, 2, lg2), MVote(2, 2, 2, lg2),
      MVote(1, 2, 2, L1), MVote(0, 2, 2, L1) }

\* A small, representative set of logs for the free node.
CtiLogs ==
    { << >>, L1, << Ent(1, "cmd") >>, << NoopEntry(2) >>,
      << NoopEntry(1), Ent(1, "cmd") >> }

\* Node 0: the term-1 leader, with the commit it justified.
CtiHost0 ==
    [ term |-> 1, vote |-> 0, role |-> "Leader", log |-> L1, commit |-> 1,
      votes |-> {0, 1}, vote_logs |-> [x \in {0, 1} |-> << >>],
      crec |-> Rec1, read_seq |-> 0 ]

\* Node 1: a term-1 follower that acked the leader's log; its term, vote and
\* commit index are free.
CtiHosts1 ==
    { [ term |-> t, vote |-> vt, role |-> "Follower", log |-> L1, commit |-> cm,
        votes |-> {}, vote_logs |-> EmptyFn,
        crec |-> IF cm > 0 THEN Rec1 ELSE ZeroRec, read_seq |-> 0 ]
      : t \in 1 .. MaxTerm, vt \in {0, 2, Nil}, cm \in {0, 1} }

\* Node 2: either a follower at any term with any of CtiLogs, or the term-2
\* candidate with any collected vote set.
CtiHosts2(lg2) ==
    { [ term |-> t, vote |-> Nil, role |-> "Follower", log |-> lg2, commit |-> 0,
        votes |-> {}, vote_logs |-> EmptyFn, crec |-> ZeroRec, read_seq |-> 0 ]
      : t \in 0 .. MaxTerm }
    \cup
    { [ term |-> 2, vote |-> 2, role |-> "Candidate", log |-> lg2, commit |-> 0,
        votes |-> V, vote_logs |-> [x \in V |-> IF x = 2 THEN lg2 ELSE L1],
        crec |-> ZeroRec, read_seq |-> 0 ]
      : V \in SUBSET node_ids }

\* The seed family: the post-term-1-commit configuration, with node 1's
\* term/vote/commit, node 2's whole state, and the term-2 election messages
\* free.  Every member satisfies TypeOK by construction.  About 10^4 states.
CtiSeed ==
    /\ leader_log  = [t \in {1} |-> L1]
    /\ leader_of   = [t \in {1} |-> 0]
    /\ voters      = [t \in {1} |-> {0, 1}]
    /\ elect_log   = [t \in {1} |-> << >>]
    /\ elect_votes = [t \in {1} |-> [x \in {0, 1} |-> << >>]]
    /\ commits = { Rec1 }
    /\ reads = {}
    /\ read_hwm = EmptyFn
    /\ \E lg2 \in CtiLogs :
           /\ \E extra \in SUBSET CtiExtra(lg2) : net = CtiNet \cup extra
           /\ \E h1 \in CtiHosts1 : \E h2 \in CtiHosts2(lg2) :
                  hosts = [i \in node_ids |->
                              IF i = 0 THEN CtiHost0
                              ELSE IF i = 1 THEN h1 ELSE h2]

\* Per-conjunct inductiveness: seed with the conjunct under test alone, take
\* one step, check the same conjunct on the successor.  A hit is a
\* counterexample to *that conjunct's* inductiveness, which says nothing
\* about `inv` as a whole (the Verus proof establishes only the conjunction).
CtiInit_wf                  == CtiSeed /\ inv_wf
CtiInit_hosts               == CtiSeed /\ inv_hosts
CtiInit_msgs                == CtiSeed /\ inv_msgs
CtiInit_lterms              == CtiSeed /\ inv_lterms
CtiInit_ack_persist         == CtiSeed /\ inv_ack_persist
CtiInit_vote_persist        == CtiSeed /\ inv_vote_persist
CtiInit_commits             == CtiSeed /\ inv_commits
CtiInit_leader_completeness == CtiSeed /\ inv_leader_completeness
CtiInit_commit_msgs         == CtiSeed /\ inv_commit_msgs
CtiInit_host_commits        == CtiSeed /\ inv_host_commits
CtiInit_commit_leaders      == CtiSeed /\ inv_commit_leaders
CtiInit_reads               == CtiSeed /\ inv_reads

\* The whole invariant over the same family: this one should find nothing,
\* because `inv` is inductive (safety.rs `step_preserves_inv`).
CtiInit_all == CtiSeed /\ Inv

=============================================================================
