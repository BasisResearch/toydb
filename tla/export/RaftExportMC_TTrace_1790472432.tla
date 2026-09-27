---- MODULE RaftExportMC_TTrace_1790472432 ----
EXTENDS Sequences, TLCExt, RaftExportMC, Toolbox, Naturals, TLC

_expression ==
    LET RaftExportMC_TEExpression == INSTANCE RaftExportMC_TEExpression
    IN RaftExportMC_TEExpression!expression
----

_trace ==
    LET RaftExportMC_TETrace == INSTANCE RaftExportMC_TETrace
    IN RaftExportMC_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        elect_votes = (<<(0 :> <<>> @@ 2 :> <<>>), (0 :> <<>> @@ 1 :> <<>>)>>)
        /\
        voters = (<<{0, 2}, {0, 1}>>)
        /\
        leader_of = (<<2, 0>>)
        /\
        hosts = (<<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 1, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)]], [term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<[term |-> 1, cmd |-> [tag |-> "None"]]>>, read_seq |-> 1, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 2}, vote_logs |-> (0 :> <<>> @@ 2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>)
        /\
        leader_log = (<<<<[term |-> 1, cmd |-> [tag |-> "None"]]>>, <<[term |-> 2, cmd |-> [tag |-> "None"]]>>>>)
        /\
        elect_log = (<<<<>>, <<>>>>)
        /\
        reads = ({[term |-> 1, born |-> {[term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)]}, seq |-> 1]})
        /\
        commits = ({[term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)]})
        /\
        read_hwm = (<<1>>)
        /\
        net = ({[term |-> 1, tag |-> "Read", seq |-> 1], [term |-> 2, rec |-> [term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)], tag |-> "Commit", ci |-> 1], [term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 2, tag |-> "Ack", v |-> 0, mi |-> 1], [term |-> 2, tag |-> "Ack", v |-> 1, mi |-> 1], [term |-> 1, tag |-> "ReadConfirm", v |-> 2, seq |-> 1], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>], [term |-> 2, tag |-> "Append", base |-> 0, bterm |-> 0, entries |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>]})
        /\
        n = (3)
    )
----

_init ==
    /\ reads = _TETrace[1].reads
    /\ leader_log = _TETrace[1].leader_log
    /\ leader_of = _TETrace[1].leader_of
    /\ n = _TETrace[1].n
    /\ read_hwm = _TETrace[1].read_hwm
    /\ net = _TETrace[1].net
    /\ hosts = _TETrace[1].hosts
    /\ elect_votes = _TETrace[1].elect_votes
    /\ voters = _TETrace[1].voters
    /\ elect_log = _TETrace[1].elect_log
    /\ commits = _TETrace[1].commits
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ reads  = _TETrace[i].reads
        /\ reads' = _TETrace[j].reads
        /\ leader_log  = _TETrace[i].leader_log
        /\ leader_log' = _TETrace[j].leader_log
        /\ leader_of  = _TETrace[i].leader_of
        /\ leader_of' = _TETrace[j].leader_of
        /\ n  = _TETrace[i].n
        /\ n' = _TETrace[j].n
        /\ read_hwm  = _TETrace[i].read_hwm
        /\ read_hwm' = _TETrace[j].read_hwm
        /\ net  = _TETrace[i].net
        /\ net' = _TETrace[j].net
        /\ hosts  = _TETrace[i].hosts
        /\ hosts' = _TETrace[j].hosts
        /\ elect_votes  = _TETrace[i].elect_votes
        /\ elect_votes' = _TETrace[j].elect_votes
        /\ voters  = _TETrace[i].voters
        /\ voters' = _TETrace[j].voters
        /\ elect_log  = _TETrace[i].elect_log
        /\ elect_log' = _TETrace[j].elect_log
        /\ commits  = _TETrace[i].commits
        /\ commits' = _TETrace[j].commits

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("RaftExportMC_TTrace_1790472432.json", _TETrace)

=============================================================================

 Note that you can extract this module `RaftExportMC_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `RaftExportMC_TEExpression.tla` file takes precedence 
  over the module `RaftExportMC_TEExpression` below).

---- MODULE RaftExportMC_TEExpression ----
EXTENDS Sequences, TLCExt, RaftExportMC, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `RaftExportMC` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        reads |-> reads
        ,leader_log |-> leader_log
        ,leader_of |-> leader_of
        ,n |-> n
        ,read_hwm |-> read_hwm
        ,net |-> net
        ,hosts |-> hosts
        ,elect_votes |-> elect_votes
        ,voters |-> voters
        ,elect_log |-> elect_log
        ,commits |-> commits
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_readsUnchanged |-> reads = reads'
        
        \* Format the `reads` variable as Json value.
        \* ,_readsJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(reads)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_readsModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].reads # _TETrace[s-1].reads
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE RaftExportMC_TETrace ----
\*EXTENDS IOUtils, RaftExportMC, TLC
\*
\*trace == IODeserialize("RaftExportMC_TTrace_1790472432.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE RaftExportMC_TETrace ----
EXTENDS RaftExportMC, TLC

trace == 
    <<
    ([elect_votes |-> <<>>,voters |-> <<>>,leader_of |-> <<>>,hosts |-> <<[term |-> 0, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "None"], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 0, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "None"], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 0, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "None"], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<>>,elect_log |-> <<>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {},n |-> 3]),
    ([elect_votes |-> <<>>,voters |-> <<>>,leader_of |-> <<>>,hosts |-> <<[term |-> 0, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "None"], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 0, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "None"], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {2}, vote_logs |-> (2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<>>,elect_log |-> <<>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>]},n |-> 3]),
    ([elect_votes |-> <<>>,voters |-> <<>>,leader_of |-> <<>>,hosts |-> <<[term |-> 1, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 0, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "None"], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {2}, vote_logs |-> (2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<>>,elect_log |-> <<>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>]},n |-> 3]),
    ([elect_votes |-> <<>>,voters |-> <<>>,leader_of |-> <<>>,hosts |-> <<[term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {0}, vote_logs |-> (0 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 0, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "None"], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {2}, vote_logs |-> (2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<>>,elect_log |-> <<>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>]},n |-> 3]),
    ([elect_votes |-> <<>>,voters |-> <<>>,leader_of |-> <<>>,hosts |-> <<[term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {0}, vote_logs |-> (0 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {2}, vote_logs |-> (2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<>>,elect_log |-> <<>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>]},n |-> 3]),
    ([elect_votes |-> <<>>,voters |-> <<>>,leader_of |-> <<>>,hosts |-> <<[term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {2}, vote_logs |-> (2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<>>,elect_log |-> <<>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>]},n |-> 3]),
    ([elect_votes |-> (2 :> (0 :> <<>> @@ 1 :> <<>>)),voters |-> (2 :> {0, 1}),leader_of |-> (2 :> 0),hosts |-> <<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {2}, vote_logs |-> (2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> (2 :> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>),elect_log |-> (2 :> <<>>),reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>]},n |-> 3]),
    ([elect_votes |-> (2 :> (0 :> <<>> @@ 1 :> <<>>)),voters |-> (2 :> {0, 1}),leader_of |-> (2 :> 0),hosts |-> <<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Candidate"], commit |-> 0, votes |-> {0, 2}, vote_logs |-> (0 :> <<>> @@ 2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> (2 :> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>),elect_log |-> (2 :> <<>>),reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>]},n |-> 3]),
    ([elect_votes |-> <<(0 :> <<>> @@ 2 :> <<>>), (0 :> <<>> @@ 1 :> <<>>)>>,voters |-> <<{0, 2}, {0, 1}>>,leader_of |-> <<2, 0>>,hosts |-> <<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<[term |-> 1, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 2}, vote_logs |-> (0 :> <<>> @@ 2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<<<[term |-> 1, cmd |-> [tag |-> "None"]]>>, <<[term |-> 2, cmd |-> [tag |-> "None"]]>>>>,elect_log |-> <<<<>>, <<>>>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>]},n |-> 3]),
    ([elect_votes |-> <<(0 :> <<>> @@ 2 :> <<>>), (0 :> <<>> @@ 1 :> <<>>)>>,voters |-> <<{0, 2}, {0, 1}>>,leader_of |-> <<2, 0>>,hosts |-> <<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 2, log |-> <<>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<[term |-> 1, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 2}, vote_logs |-> (0 :> <<>> @@ 2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<<<[term |-> 1, cmd |-> [tag |-> "None"]]>>, <<[term |-> 2, cmd |-> [tag |-> "None"]]>>>>,elect_log |-> <<<<>>, <<>>>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>], [term |-> 2, tag |-> "Append", base |-> 0, bterm |-> 0, entries |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>]},n |-> 3]),
    ([elect_votes |-> <<(0 :> <<>> @@ 2 :> <<>>), (0 :> <<>> @@ 1 :> <<>>)>>,voters |-> <<{0, 2}, {0, 1}>>,leader_of |-> <<2, 0>>,hosts |-> <<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<[term |-> 1, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 2}, vote_logs |-> (0 :> <<>> @@ 2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<<<[term |-> 1, cmd |-> [tag |-> "None"]]>>, <<[term |-> 2, cmd |-> [tag |-> "None"]]>>>>,elect_log |-> <<<<>>, <<>>>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 2, tag |-> "Ack", v |-> 1, mi |-> 1], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>], [term |-> 2, tag |-> "Append", base |-> 0, bterm |-> 0, entries |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>]},n |-> 3]),
    ([elect_votes |-> <<(0 :> <<>> @@ 2 :> <<>>), (0 :> <<>> @@ 1 :> <<>>)>>,voters |-> <<{0, 2}, {0, 1}>>,leader_of |-> <<2, 0>>,hosts |-> <<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<[term |-> 1, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 2}, vote_logs |-> (0 :> <<>> @@ 2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<<<[term |-> 1, cmd |-> [tag |-> "None"]]>>, <<[term |-> 2, cmd |-> [tag |-> "None"]]>>>>,elect_log |-> <<<<>>, <<>>>>,reads |-> {},commits |-> {},read_hwm |-> <<>>,net |-> {[term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 2, tag |-> "Ack", v |-> 0, mi |-> 1], [term |-> 2, tag |-> "Ack", v |-> 1, mi |-> 1], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>], [term |-> 2, tag |-> "Append", base |-> 0, bterm |-> 0, entries |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>]},n |-> 3]),
    ([elect_votes |-> <<(0 :> <<>> @@ 2 :> <<>>), (0 :> <<>> @@ 1 :> <<>>)>>,voters |-> <<{0, 2}, {0, 1}>>,leader_of |-> <<2, 0>>,hosts |-> <<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 1, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)]], [term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<[term |-> 1, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 2}, vote_logs |-> (0 :> <<>> @@ 2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<<<[term |-> 1, cmd |-> [tag |-> "None"]]>>, <<[term |-> 2, cmd |-> [tag |-> "None"]]>>>>,elect_log |-> <<<<>>, <<>>>>,reads |-> {},commits |-> {[term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)]},read_hwm |-> <<>>,net |-> {[term |-> 2, rec |-> [term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)], tag |-> "Commit", ci |-> 1], [term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 2, tag |-> "Ack", v |-> 0, mi |-> 1], [term |-> 2, tag |-> "Ack", v |-> 1, mi |-> 1], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>], [term |-> 2, tag |-> "Append", base |-> 0, bterm |-> 0, entries |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>]},n |-> 3]),
    ([elect_votes |-> <<(0 :> <<>> @@ 2 :> <<>>), (0 :> <<>> @@ 1 :> <<>>)>>,voters |-> <<{0, 2}, {0, 1}>>,leader_of |-> <<2, 0>>,hosts |-> <<[term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Leader"], commit |-> 1, votes |-> {0, 1}, vote_logs |-> (0 :> <<>> @@ 1 :> <<>>), crec |-> [term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)]], [term |-> 2, log |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>, read_seq |-> 0, vote |-> [tag |-> "Some", v0 |-> 0], role |-> [tag |-> "Follower"], commit |-> 0, votes |-> {}, vote_logs |-> <<>>, crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]], [term |-> 1, log |-> <<[term |-> 1, cmd |-> [tag |-> "None"]]>>, read_seq |-> 1, vote |-> [tag |-> "Some", v0 |-> 2], role |-> [tag |-> "Leader"], commit |-> 0, votes |-> {0, 2}, vote_logs |-> (0 :> <<>> @@ 2 :> <<>>), crec |-> [term |-> 0, ci |-> 0, q |-> <<>>]]>>,leader_log |-> <<<<[term |-> 1, cmd |-> [tag |-> "None"]]>>, <<[term |-> 2, cmd |-> [tag |-> "None"]]>>>>,elect_log |-> <<<<>>, <<>>>>,reads |-> {[term |-> 1, born |-> {[term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)]}, seq |-> 1]},commits |-> {[term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)]},read_hwm |-> <<1>>,net |-> {[term |-> 1, tag |-> "Read", seq |-> 1], [term |-> 2, rec |-> [term |-> 2, ci |-> 1, q |-> (0 :> 1 @@ 1 :> 1)], tag |-> "Commit", ci |-> 1], [term |-> 1, tag |-> "Campaign", c |-> 2, clog |-> <<>>], [term |-> 2, tag |-> "Campaign", c |-> 0, clog |-> <<>>], [term |-> 2, tag |-> "Ack", v |-> 0, mi |-> 1], [term |-> 2, tag |-> "Ack", v |-> 1, mi |-> 1], [term |-> 1, tag |-> "ReadConfirm", v |-> 2, seq |-> 1], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 0, vlog |-> <<>>], [term |-> 1, tag |-> "Vote", c |-> 2, v |-> 2, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 0, vlog |-> <<>>], [term |-> 2, tag |-> "Vote", c |-> 0, v |-> 1, vlog |-> <<>>], [term |-> 2, tag |-> "Append", base |-> 0, bterm |-> 0, entries |-> <<[term |-> 2, cmd |-> [tag |-> "None"]]>>]},n |-> 3])
    >>
----


=============================================================================

---- CONFIG RaftExportMC_TTrace_1790472432 ----
CONSTANTS
    N = 3
    MaxTerm = 2
    MaxLog = 1
    MaxRead = 1
    MaxMsgs = 12
    NCommands = 1
    Dom_Option_Seq_u8_Some_v0 <- MC_Dom_Option_Seq_u8_Some_v0
    Dom_TStep_BumpTerm_term <- MC_Dom_TStep_BumpTerm_term
    Dom_TStep_LeaderCommit_q <- MC_Dom_TStep_LeaderCommit_q

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Sun Sep 27 01:28:29 UTC 2026