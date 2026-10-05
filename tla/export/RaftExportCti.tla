--------------------------- MODULE RaftExportCti ---------------------------
(***************************************************************************)
(* Raft_cti.tla's inductiveness probe on the export: the same seed family  *)
(* (CtiSeed), restated in the export's representation, conjoined with one  *)
(* inv_* conjunct as INIT; one step of the exported `next`; the same       *)
(* conjunct checked on the successor.  Only the representation changes:    *)
(* hosts is a sequence (node i at index i+1), messages and roles are       *)
(* records tagged by variant, a vote is an Option record, and the free     *)
(* node's client command (Raft_cti's SomeCmd) is the payload <<1>>.        *)
(***************************************************************************)
EXTENDS RaftExportMC

\* `next` rather than `Next == next /\ TypeOK'`: TLC then names the variant's
\* disjunct a violating step took.  TypeOK' only keeps the state's integer
\* fields in their types, which every step does (Verus proves it).
CtiNext == next

CtiOneStep == TLCGet("level") < 2

None      == [tag |-> "None"]
Some(x)   == [tag |-> "Some", v0 |-> x]
Role(r)   == [tag |-> r]
SomeCmd   == Some(<<1>>)
NoopEntry(t) == [term |-> t, cmd |-> None]
Ent(t, c)    == [term |-> t, cmd |-> c]
EmptyFn   == << >>

MCampaign(c, t, clog)  == [tag |-> "Campaign", c |-> c, term |-> t, clog |-> clog]
MVote(v, c, t, vlog)   == [tag |-> "Vote", v |-> v, c |-> c, term |-> t, vlog |-> vlog]
MCommit(t, ci, rec)    == [tag |-> "Commit", term |-> t, ci |-> ci, rec |-> rec]
MAck(v, t, mi)         == [tag |-> "Ack", v |-> v, term |-> t, mi |-> mi]

L1      == << NoopEntry(1) >>
ZeroRec == [term |-> 0, ci |-> 0, q |-> EmptyFn]
Rec1    == [term |-> 1, ci |-> 1, q |-> [x \in {0, 1} |-> 1]]

CtiNet ==
    { MCampaign(0, 1, << >>), MVote(0, 0, 1, << >>), MVote(1, 0, 1, << >>),
      MAck(0, 1, 1), MAck(1, 1, 1), MCommit(1, 1, Rec1) }

CtiExtra(lg2) ==
    { MCampaign(2, 2, lg2), MVote(2, 2, 2, lg2),
      MVote(1, 2, 2, L1), MVote(0, 2, 2, L1) }

CtiLogs ==
    { << >>, L1, << Ent(1, SomeCmd) >>, << NoopEntry(2) >>,
      << NoopEntry(1), Ent(1, SomeCmd) >> }

CtiHost0 ==
    [ term |-> 1, vote |-> Some(0), role |-> Role("Leader"), log |-> L1, commit |-> 1,
      votes |-> {0, 1}, vote_logs |-> [x \in {0, 1} |-> << >>],
      crec |-> Rec1, read_seq |-> 0 ]

CtiHosts1 ==
    { [ term |-> t, vote |-> vt, role |-> Role("Follower"), log |-> L1, commit |-> cm,
        votes |-> {}, vote_logs |-> EmptyFn,
        crec |-> IF cm > 0 THEN Rec1 ELSE ZeroRec, read_seq |-> 0 ]
      : t \in 1 .. MaxTerm, vt \in {Some(0), Some(2), None}, cm \in {0, 1} }

CtiHosts2(lg2) ==
    { [ term |-> t, vote |-> None, role |-> Role("Follower"), log |-> lg2, commit |-> 0,
        votes |-> {}, vote_logs |-> EmptyFn, crec |-> ZeroRec, read_seq |-> 0 ]
      : t \in 0 .. MaxTerm }
    \cup
    { [ term |-> 2, vote |-> Some(2), role |-> Role("Candidate"), log |-> lg2, commit |-> 0,
        votes |-> V, vote_logs |-> [x \in V |-> IF x = 2 THEN lg2 ELSE L1],
        crec |-> ZeroRec, read_seq |-> 0 ]
      : V \in SUBSET Nodes }

CtiSeed ==
    /\ n = N
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
                  hosts = << CtiHost0, h1, h2 >>

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
CtiInit_all ==
    CtiSeed /\ inv_wf /\ inv_hosts /\ inv_msgs /\ inv_lterms /\ inv_ack_persist
            /\ inv_vote_persist /\ inv_commits /\ inv_leader_completeness
            /\ inv_commit_msgs /\ inv_host_commits /\ inv_commit_leaders /\ inv_reads
\* inv_ack_persist on the acks whose term has a leader log (ack_msg_ok's own
\* domain clause).  The export reads safety.rs's `s.leader_log[t]` as
\* `leader_log[t]`, which TLC cannot evaluate off the domain, where Verus's
\* total Map has an unspecified value (Raft.tla reads LL(t) = << >> there,
\* its (A5)).  This is the part of the conjunct that does not depend on
\* that value, probed from CtiInit_ack_persist; see EXPORT.md.
inv_ack_persist_dom ==
    \A m \in net : (m.tag = "Ack" /\ m.term \in DOMAIN leader_log)
                    => ack_persist_ok(m.v, m.term, m.mi)
=============================================================================
