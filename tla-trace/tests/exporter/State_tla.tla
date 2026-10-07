---- MODULE State_tla ----
\* Exported by verus -V tla-export from the Verus model in `encoding`.
\* Mapping: structs are records; enum values are records with a `tag`;
\* Seq is a 1-based sequence (every index shifted once); Set is a set;
\* Map is a function (dom = DOMAIN, insert = :> @@); an ISet or IMap is a Set or
\* Map; Multiset is a function from the elements it holds to their counts (each
\* above 0, count = the value or 0); Option is a record tagged
\* None/Some with field v0; nat/int/uN are Int, and TypeOK keeps each variable
\* in its type's range (conjoined to Init, primed to Next); a spec fn is an operator, its
\* pre/post state parameters dropped and read as the unprimed/primed variables;
\* a quantifier is bounded from its guard, or from a CONSTANT Dom_<Type>.
\* What the export could not express is an Assert(FALSE, ...) that stops TLC
\* wherever it is evaluated.
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLES record, choice
vars == <<record, choice>>

\* encoding::init, tla-trace/tests/exporter/encoding.rs:17:1: 17:40 (#0)
init ==
    ((record = [tag_ |-> 0, tag__ |-> 7, unit |-> <<>>]) /\ (choice = [tag |-> "A", tag_ |-> 0]))

\* encoding::t_set, tla-trace/tests/exporter/encoding.rs:21:1: 21:69 (#0)
t_set(r_type) ==
    ((record' = [tag_ |-> r_type, tag__ |-> record.tag__, unit |-> <<>>]) /\ (choice' = [tag |-> "A", tag_ |-> r_type]))

\* encoding::next, tla-trace/tests/exporter/encoding.rs:25:1: 25:55 (#0)
next ==
    (\E n \in (IF (1) > 0 THEN (1) ELSE 0)..2 : (((1 <= n) /\ (n <= 2)) /\ t_set(n)))

\* The state's integer fields stay within their types, as in Verus.
TypeOK ==
    /\ ((record.tag_ >= 0) /\ (record.tag__ >= 0))
    /\ (choice.tag = "A" => (choice.tag_ >= 0))
Init == init /\ TypeOK
Next == next /\ TypeOK'
Spec == Init /\ [][Next]_vars
=============================
