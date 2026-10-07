# tla-trace

Annotate synchronous Rust methods and check their observed transitions against a
TLA+ export. The runtime is independent of toyDB and Verus. `trace_step!` remains
available for existing callers. The attribute is under `instrument` because Rust
uses one namespace for attribute and function-like macros.

```rust
use tla_trace::{Observe, Trace, Value};
use tla_trace::instrument::trace_step;

#[derive(Observe)]
struct Counter {
    x: u64,
    #[observe(skip)]
    trace: Trace,
}

#[trace_step]
impl Counter {
    #[trace_skip]
    fn new() -> Self { Self { x: 0, trace: Trace::default() } }
    fn add(&mut self, amount: u64) {
        self.increment(amount);
    }
    fn increment(&mut self, amount: u64) { self.x += amount; }
    #[trace_skip]
    const fn value(&self) -> u64 { self.x }
}

# let dir = tempfile::tempdir().unwrap();
let mut counter = Counter::new();
counter.trace = Trace::object(
    dir.path(), Some("counter-a"),
    Value::object([("module", Value::from("Counter")),
                   ("export", Value::from("counter"))]),
    true, // diff mode; header still observes the whole initial state
    |cx| counter.observe(cx),
).unwrap();
counter.add(3); // just t_add(amount=3), not t_increment
assert_eq!(counter.value(), 3);
```

`Trace::object` creates `<id>.ndjson`; pass `None` for a process/counter ID.
An explicit ID may contain letters, digits, `-`, and `_`. Existing files are
rejected, never silently overwritten. Give each independent object its own
handle. Moving an object between threads retains its identity. Cloning a handle
intentionally shares its identity; when cloning a container, create a new handle
for the clone. A default handle is disabled and does not evaluate observations
or parameters. Dropping the last handle closes its file.

Calls nested through the same handle on the same thread are suppressed. Calls
through another object's handle still emit. A reservation serializes calls from
other threads until completion, including state observation; use the same
handle for all operations on shared state. This serialization can perturb races.
Observers must not call instrumented methods or acquire locks in an order that
conflicts with the implementation. As with ordinary locks, opposite-order nested
calls across multiple objects can deadlock.

## Attributes

On an `impl`, all methods are instrumented; `#[trace_skip]` opts a member out.
An individually attributed method overrides the impl defaults. Existing `cfg`
attributes and doc comments are preserved. Attributes on methods work without
an impl attribute. Defaults are:

- Handle: `self.trace.clone()`.
- Transition name: `t_<method name>`.
- Parameters: named arguments, observed **before** the body.
- State: `Observe::observe(self, cx)` **after** the body.

Override any of these with expressions:

```rust
# use tla_trace::{Trace, Value, instrument::trace_step};
# struct Counter { trace: Trace, x: u64 }
impl Counter {
    #[trace_step(step = "t_increment", log = self.trace.clone(),
        params = Value::object([("n", Value::from(amount))]),
        state = Value::object([("x", Value::from(self.x))]))]
    fn add(&mut self, amount: u64) { self.x += amount; }
}
```

The `params` and `state` expressions have a mutable `cx: &mut Context` for
interning/observation. State expressions can also refer to the method's owned
`result`. Explicit `return` and `?` keep their usual method-level behavior.
Returning `Err` is a completed call and is observed by default; a panic is not.
Arguments consumed by the body are available only to pre-call `params`, unless
retained separately by the implementation.

For a core call that implements zero or several model transitions, use
`events = <Vec<Event>>` instead of `params` and `state`. This expression runs only
for an enabled outer call, after the body, and has access to `result` and `self`.
`Event::new(step, params, state)` names each transition and observation. A single
begin/end frame encloses the list, even an empty list. The begin's name identifies
the Rust operation and need not itself name a model transition. An empty event
list explicitly asserts that the call caused no observable model transition.

The attribute requires a safe, non-const, synchronous method with `&self` or
`&mut self`. It rejects async methods (cancellation/suspension requires a different
protocol), consuming receivers, and recognizable returned references or opaque
borrowed iterators. Use an owned-result wrapper or `#[trace_skip]`. Never use
unsafe pointer reads to work around a returned mutable borrow: writes through it
happen *after* the method returned and need their own modeled operation. Type
aliases may cause the borrow checker to reject an unsupported return type instead
of the macro's diagnostic. Constructors and other associated functions require
`#[trace_skip]` inside an attributed impl (as in the example above); the header
captures initialization. Panics before `Trace::object` opens a log cannot be detected.

```compile_fail
use tla_trace::{Trace, instrument::trace_step};
struct Buffer { trace: Trace, data: Vec<u8> }
impl Buffer {
    #[trace_step]
    fn get(&mut self) -> &mut u8 { &mut self.data[0] }
}
```

```compile_fail
use tla_trace::{Trace, instrument::trace_step};
struct Counter { trace: Trace }
#[trace_step]
impl Counter { const fn size(&self) -> usize { 0 } }
```

## Observe and value encoding

`Observe::observe(&self, &mut Context) -> Value` can be implemented manually, or
derived for structs, tuple structs, and enums. Field annotations are
`#[observe(skip)]`, `#[observe(rename = "model_name")]`,
`#[observe(intern)]`, and `#[observe(with = path_to_encoder)]` (a function taking
`&FieldType, &mut Context`). Skipped fields stay unobserved, not zero-valued.

Default field names follow the exporter: `tag` becomes `tag_`, `tag_` becomes
`tag__`, and so on. `rename` specifies the final encoded model name. Duplicate
encoded names and a field renamed to the reserved `tag` are compile errors.

```compile_fail
use tla_trace::Observe;
#[derive(Observe)]
struct Duplicate {
    tag: u64, // encodes as tag_
    #[observe(rename = "tag_")]
    other: u64,
}
```

```compile_fail
use tla_trace::Observe;
#[derive(Observe)]
enum Reserved {
    A { #[observe(rename = "tag")] value: u64 },
    B,
}
```

| Rust/model value | JSON value |
| --- | --- |
| integers, bool, string, char | number, boolean, string, one-character string |
| record | object with model field names |
| enum | `{"tag":"Variant", "named":value}` or positional `v0`, `v1`, … |
| Option | `{"tag":"None"}` or `{"tag":"Some","v0":value}` |
| sequence / array / tuple | array, interpreted by TLA at positions **1..Len** |
| set | array of elements |
| map | array of `[key,value]` pairs |

The unit tuple `()` is `[]`; an empty struct is `{}`.

`Observe` supports slices, arrays, Vec/VecDeque, BTreeSet/HashSet,
BTreeMap/HashMap, Option, Box, references, and pairs. Set/map iteration order is
not a semantic order. Scalars retain their values; no truncation to TLC's integer
range is performed. TLC still requires numbers in its supported range.

The derive interns bare generic elements `T` and those inside standard
Vec/VecDeque, Option, sets, and maps by default. It requires `T: Clone + Eq + Send + 'static`, without `Observe`, `Debug`, or byte access. Equal values get equal positive
IDs in a type-specific table shared across observations of this log. For other
shapes use `with` and `cx.intern(value)`. The equality table retains clones for the
log's lifetime and currently uses linear lookup. For generic method parameters,
use `params = ... cx.intern(&argument) ...` to share that same encoding; ordinary
parameters use `Observe`, not automatic interning. A model must interpret interned
IDs as opaque identities, not as the element's numeric value.

Object observations are partial, as in the exporter. JSON arrays are whole
collections; the exporter's *partial sequence object keys* use Verus's zero-based
indices, which is separate from TLA's one-based array positions. The derive emits
whole sequences and no ghost fields.

## Wire format and compatibility

New logs have a header with `"format":"tla-trace-v2"` and the full initial
observation in `state`. `start(path, header)` still opens one compatibility log
per thread; `trace_step!`, `emit`, `active`, and `finish` continue to work. For
attribute calls into that log use `log = tla_trace::thread_log()`.

```json
{"module":"Counter","export":"counter","format":"tla-trace-v2","state":{"x":0}}
{"begin":1,"step":"t_add","params":{"amount":3}}
{"step":"t_add","params":{"amount":3},"diff":{"x":3},"remove":[]}
{"end":1}
```

Without diff mode the middle line remains the original
`{"step":...,"params":...,"state":...}`. Begin IDs increase per log, not per
thread. Begin is written and flushed before the body. Completion writes its model
step(s), then an end with the same ID. All lines are flushed. Unwinding releases
the reservation without an end, so even a caught panic followed by successful
calls remains a divergence. Process termination leaves the same evidence; this
is not an `fsync` guarantee against power loss. Legacy explicit emissions have
no framing and therefore cannot detect an interrupted operation.

Diffs replace **whole top-level fields**, not nested patches. `remove` lists
fields that became unobserved. The reader must carry unchanged fields forward;
sending a diff directly to the old partial-observation checker would weaken the
check. Arrays and nested records that changed are replaced whole. This saves
repeated unchanged fields, but does not promise sublinear logs for a single
sequence field that grows every step.

Normalize before calling an existing exported trace spec or `tlc_conform`:

```sh
python3 tla-trace/normalize.py input.ndjson normalized.ndjson
# Pass normalized.ndjson to tlc_conform, only if normalization succeeded.
```

The adapter accepts legacy logs too, including omitted `params` and `state`
fields (the model supplies parameter domains; omitted state observes nothing).
It validates framing, rejects unknown record fields, reconstructs full
observations from diffs, and strips only v2
metadata. An unmatched begin reports the affected model step and Rust operation,
returns nonzero, and writes no new output. It never treats the completed prefix
of a panicking call as a passing trace. Older tools cannot read v2 directly;
the repo runner performs normalization automatically. If reusing an output path,
check the command's exit status rather than accidentally checking a stale file.

## Raft worked example and validation

`src/raft/node_steps.rs` adapts the verified core to the shell with 15 attributed
methods. A cluster, rather than an individual node, is the modeled object: its
network history links every node's steps, so independent per-node files would not
be checkable against this global Raft model. The goldenscript harness keeps its
one cluster log per script. Other models use `Trace::object` per instance.

The adapters keep compound heartbeat/commit transitions and intermediate omitted
commit fields intact. `refine.rs` retains its manual observer because observing
Raft involves fallible storage reads and role-dependent partial fields, not a
simple structural derive. The restart adapter observes recovered state; storage
recovery itself still occurs before that adapter and is not panic-framed.

```sh
cargo test --manifest-path tla-trace/Cargo.toml
python3 -m unittest discover -s tla-trace -p 'test_*.py'
cargo test --lib
TLA2TOOLS_JAR=/path/to/tla2tools.jar cargo test --manifest-path tla-trace/Cargo.toml --test exporter -- --ignored
TLA2TOOLS_JAR=/path/to/tla2tools.jar bash tla/conform.sh
TLA2TOOLS_JAR=/path/to/tla2tools.jar bash tla/conform.sh tla/traces/*.ndjson
```

Each TLC process is bounded by `TLC_TIMEOUT` seconds (default 120). The runner
checks the complete normalized log, including negative fixtures. See
[VALIDATION.md](VALIDATION.md) for measured coverage and instrumentation counts.
