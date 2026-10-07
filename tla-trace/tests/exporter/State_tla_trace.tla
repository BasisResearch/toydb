---- MODULE State_tla_trace ----
\* Trace validation for State_tla, the export of `encoding` (verus -V tla-export).
\* The log is newline-delimited JSON: a header line naming the module
\* ({"module": "State_tla", "export": "encoding"}, optionally "state": the
\* observed initial state; another module or export stops TLC), then one line per step:
\* {"step": "<t_* name>", "params": {...}, "state": {...}}. A step is named by
\* its spec fn's last segment or full path, by the full path alone when two
\* steps share the last segment; a parameter the step does not declare stops
\* TLC. Values are in the export's encoding: a struct or enum value is an
\* object (an enum's with its "tag"), a Seq an array, a Set an array of its
\* elements, a Map an array of [key, value] pairs, a tuple an array, a struct
\* without fields {} (or {"tag": "unit"}). An object
\* observed in the state is partial: only the fields it names are compared, so
\* a ghost field is left out of the log and free in the model (an enum's tag
\* too: its fields are then compared under whichever variant the model has);
\* a key naming no field of its type stops TLC, as one naming no state field
\* does; a Seq may be observed partially as an object keyed by the Verus index
\* ("0", "1", ...; {} observes nothing, [] is the empty Seq; a key
\* that is no index stops TLC). A key a line or the header does not define
\* stops TLC, so a misspelled "state" or "params" never observes nothing.
\* A record inside a Set element, a Map key or a parameter is decoded whole,
\* so it must name every field and an enum its tag (one left out there stops
\* TLC). A parameter left out of "params" ranges over what Next's calls to
\* the step pass it (the bound of the quantifier binding the argument, or the
\* field of a value matched against a pattern, such as a VerusSync step's
\* Dom_Step_<t>_v<i>), else its type's finite domain (not a Dom_<Type> hole,
\* which holds only what a quantifier binds, never a value a call computes);
\* with neither it must be logged, and TraceEnabled leaves the step out (the
\* report's trace steps say which, "enumerated"). A logged parameter outside
\* its domain is a step the model cannot take.
\* TraceNext selects the logged existential arm and its logged parameters.
\* Missing parameters retain their original domains; dispatch guards and
\* TypeOK are preserved. General relations retain their enclosing Next check
\* (listed in trace.general_relation_steps). Unknown names fall back to Next,
\* checking only the observed state sequence (trace.unknown_step).
\* A trace conforms when it reaches TraceAccepted; otherwise the deepest trace_i
\* is the first unexplained step; when TLC finds no initial state (0 states generated, depth 0),
\* the header is rejected.
\* A pass means the observed state sequence is a behaviour of the model.
EXTENDS State_tla, Json, TLC, Integers, Sequences

CONSTANT TraceLog  \* the log's path
VARIABLE trace_i  \* the next logged step to take

TraceLines == ndJsonDeserialize(TraceLog)
TraceHeader == TraceLines[1]
Trace == SubSeq(TraceLines, 2, Len(TraceLines))

\* Whether a JSON value is an array (TLC holds it as a tuple).
TraceIsArray(j) == SubSeq(ToString(j), 1, 2) = "<<"
TraceStateOf(e) == IF "state" \in DOMAIN e THEN e.state ELSE [k \in {} |-> 0]
\* A logged parameter, or the domain it ranges over when left out. The domain
\* holds every value Next passes it, so a logged value outside it is a step
\* the model cannot take.
TraceParam(e, k, Dec(_), D) ==
    IF "params" \in DOMAIN e /\ k \in DOMAIN e.params THEN {Dec(e.params[k])} \cap D ELSE D
\* The same for a parameter with no domain, which must be logged.
TraceParamUnbounded(e, k, Dec(_), D) ==
    IF "params" \in DOMAIN e /\ k \in DOMAIN e.params THEN {Dec(e.params[k])} ELSE D
\* Every parameter logged is one of S, the step's declared parameters (an IF,
\* not a disjunction, which TLC would take as two branches of the action).
TraceParamsDeclared(e, S) ==
    "params" \in DOMAIN e =>
        \A k \in DOMAIN e.params :
            IF k \in S THEN TRUE
            ELSE Assert(FALSE, "trace: " \o e.step \o " has no parameter " \o k)

\* Every key of a log line is one of S, so a misspelled "state" or
\* "params" stops TLC rather than observing nothing.
TraceKeys(e, S, j) ==
    \A k \in DOMAIN e :
        IF k \in S THEN TRUE
        ELSE Assert(FALSE, "trace: " \o j \o " has no key " \o k)

RECURSIVE TraceDec_Choice(_), TraceDec_Record(_), TraceDec_nat(_), TraceDec_tuple0(_), TraceObs_Choice(_, _), TraceObs_Record(_, _), TraceObs_nat(_, _), TraceObs_tuple0(_, _)

\* nat
TraceDec_nat(j) ==
    j
TraceObs_nat(v, j) ==
    v = j

\* tuple0
TraceDec_tuple0(j) ==
    <<>>
TraceObs_tuple0(v, j) ==
    Len(j) = 0

\* Record
TraceDec_Record(j) ==
    [tag_ |-> TraceDec_nat(j.tag_), tag__ |-> TraceDec_nat(j.tag__), unit |-> TraceDec_tuple0(j.unit)]
TraceObs_Record(v, j) ==
    \A k \in DOMAIN j \ {"tag"} :
        CASE k = "tag_" -> TraceObs_nat(v.tag_, j[k])
          [] k = "tag__" -> TraceObs_nat(v.tag__, j[k])
          [] k = "unit" -> TraceObs_tuple0(v.unit, j[k])
          [] OTHER -> Assert(FALSE, "trace: Record has no field " \o k)

\* Choice
TraceDec_Choice(j) ==
    IF "tag" \in DOMAIN j
    THEN CASE j.tag = "A" -> [tag |-> "A", tag_ |-> TraceDec_nat(j.tag_)]
           [] j.tag = "B" -> [tag |-> "B"]
           [] OTHER -> Assert(FALSE, "trace: Choice has no variant " \o ToString(j.tag))
    ELSE Assert(FALSE, "trace: a Choice value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_Choice(v, j) ==
    (IF "tag" \in DOMAIN j THEN v.tag = j.tag ELSE TRUE) /\ \A k \in DOMAIN j \ {"tag"} :
        CASE v.tag = "A" /\ k = "tag_" -> TraceObs_nat(v.tag_, j[k])
          [] OTHER -> IF k \in {"tag_"} THEN FALSE ELSE Assert(FALSE, "trace: Choice has no field " \o k)

TraceObservedKey(k, j) ==
    CASE k = "record" -> TraceObs_Record(record, j)
      [] k = "choice" -> TraceObs_Choice(choice, j)
      [] OTHER -> Assert(FALSE, "trace: the state has no field " \o k)
TraceObserved(j) == \A k \in DOMAIN j : TraceObservedKey(k, j[k])
\* The same of the next state: its variables primed, never the log's index.
TraceObservedKeyNext(k, j) ==
    CASE k = "record" -> TraceObs_Record(record', j)
      [] k = "choice" -> TraceObs_Choice(choice', j)
      [] OTHER -> Assert(FALSE, "trace: the state has no field " \o k)
TraceObservedNext(j) == \A k \in DOMAIN j : TraceObservedKeyNext(k, j[k])

TraceStep(e) ==
    CASE e.step \in {"t_set", "encoding::t_set"} ->
           Next /\ TraceParamsDeclared(e, {"n"}) /\ \E a1_ \in TraceParam(e, "n", TraceDec_nat, (IF (1) > 0 THEN (1) ELSE 0)..2) : t_set(a1_)
      [] OTHER -> Next

TraceInit ==
    /\ TraceKeys(TraceHeader, {"module", "export", "state"}, "the log's header")
    /\ Assert("module" \in DOMAIN TraceHeader /\ TraceHeader.module = "State_tla",
              "trace: the log's header does not name the module State_tla")
    /\ Assert("export" \in DOMAIN TraceHeader /\ TraceHeader.export = "encoding",
              "trace: the log's header does not name the export encoding")
    /\ Init
    /\ trace_i = 1
    /\ TraceObserved(TraceStateOf(TraceHeader))

TraceNext ==
    /\ trace_i <= Len(Trace)
    /\ LET e == Trace[trace_i] IN
           /\ TraceKeys(e, {"step", "params", "state"}, "a step line")
           /\ Assert("step" \in DOMAIN e, "trace: a step line names no step")
           /\ TraceStep(e)
           /\ TraceObservedNext(TraceStateOf(e))
    /\ trace_i' = trace_i + 1

TraceSpec == TraceInit /\ [][TraceNext]_<<record, choice, trace_i>>
\* The whole log was followed.
TraceAccepted == trace_i = Len(Trace) + 1

TraceStepAt == Trace[trace_i]
\* The model's steps enabled in the current state, with their parameters
\* (a step whose parameter has no finite domain is not enumerated).
TraceEnabled ==
    {r \in {[step |-> "t_set", params |-> [n |-> a1_]] : a1_ \in (IF (1) > 0 THEN (1) ELSE 0)..2} :
        ENABLED (Next /\ t_set(r.params.n))}
\* At a state where the log's next step cannot be taken: whether the logged
\* step is enabled at all, and which observed fields no successor by it matches.
TraceDiagnosis ==
    LET e == TraceStepAt IN
    [ step_enabled |-> ENABLED (Next /\ TraceStep(e)),
      unmatched |-> {k \in DOMAIN TraceStateOf(e) :
                        ~ENABLED (Next /\ TraceStep(e) /\ TraceObservedKeyNext(k, TraceStateOf(e)[k]))} ]
===================================

\* VERUS_TRACE_POLICY {"module":"State_tla_trace","index_variable":"trace_i","observables":["record","choice"],"steps":[{"step":"t_set","function":"encoding::t_set","operator":"t_set","short_name_shared":false,"params":[{"name":"n","typ":"nat","domain":"(IF (1) > 0 THEN (1) ELSE 0)..2"}],"enumerated":true}],"general_relation_steps":["t_set"],"unknown_step":"Next (state-only conformance; logged name and parameters are not checked)"}
