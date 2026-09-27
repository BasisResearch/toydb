---------------------------- MODULE RaftExportMC ----------------------------
(***************************************************************************)
(* Model-checking wrapper for GState_tla.tla, the module `verus            *)
(* -V tla-export` generates from src/raft/safety.rs.  It adds only what the *)
(* export's report asks for: a value for every hole constant, the value of *)
(* the one variable Init leaves unassigned, and a state constraint.  The   *)
(* bounds are constants, set per configuration as Raft.tla's are; every   *)
(* hole value is justified in EXPORT.md.                                   *)
(***************************************************************************)
EXTENDS GState_tla

CONSTANTS
    N,          \* cluster size (the export's n; Init leaves hosts to it)
    MaxTerm,    \* term bound
    MaxLog,     \* log-length bound
    MaxRead,    \* read-sequence bound
    MaxMsgs,    \* |net| bound
    NCommands   \* size of the command alphabet (Raft.tla's Command)

\* Command payloads: Option<Seq<u8>>; NCommands distinct one-byte strings
\* stand for Raft.tla's Command = {c1, ...}, None is the election noop.
Payloads == { <<k>> : k \in 1 .. NCommands }

Nodes == 0 .. (N - 1)
\* A commit record's ack map: a node subset to acked match indexes.
QMaps == UNION { [Q -> 0 .. MaxLog] : Q \in SUBSET Nodes }

\* ---- hole values ---------------------------------------------------------
\* The three quantities no guard in safety.rs bounds (see EXPORT.md).
\* t_propose's command payload: the NCommands-command alphabet.
MC_Dom_Option_Seq_u8_Some_v0 == Payloads
\* t_leader_commit's ack map q: Raft.tla's (A4), [Q -> 0..MaxLog] per node set.
MC_Dom_TStep_LeaderCommit_q  == QMaps
\* t_bump_term's new term, which must exceed the host's: 1..MaxTerm.
MC_Dom_TStep_BumpTerm_term   == 1 .. MaxTerm

\* ---- Init ----------------------------------------------------------------
\* safety.rs `init` fixes n >= 1 and hosts only through n (report:
\* init_unassigned = [hosts]); Raft.cfg's cluster is N nodes.
MCInit ==
    /\ n = N
    /\ hosts = [k \in 1 .. N |-> init_host]
    /\ Init

\* ---- the bounding constraint, Raft.tla's Constraint on these variables ----
MCConstraint ==
    /\ \A k \in 1 .. Len(hosts) :
           /\ hosts[k].term <= MaxTerm
           /\ Len(hosts[k].log) <= MaxLog
           /\ hosts[k].read_seq <= MaxRead
    /\ \A t \in DOMAIN leader_log : Len(leader_log[t]) <= MaxLog
    /\ Cardinality(net) <= MaxMsgs

\* Raft.tla's vacuity witnesses, on the export's variables: a commit and a
\* strictly later elected term; a read whose born set holds a later commit.
NoLC == ~(\E rec \in commits : \E u \in DOMAIN leader_log : u > rec.term)
NoR2 == ~(\E r \in reads : \E rec \in r.born : rec.term > r.term)
=============================================================================
