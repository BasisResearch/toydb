# Exporter compatibility fixture

`State_tla.tla` and `State_tla_trace.tla` are unedited output from the local
BasisResearch/verus build `0.2026.10.07.7789a50.dirty`. Tests use the committed
output so they do not require Verus. Regenerate from the repository root with
a trace-capable BasisResearch/verus binary:

```sh
VERUS_MCP_ENABLED=1 "$VERUS" tla-trace/tests/exporter/encoding.rs \
  --crate-type=lib --no-verify -V tla-export=encoding --log-dir /tmp/encoding-export
cp /tmp/encoding-export/State_tla{,_trace}.tla tla-trace/tests/exporter/
```

The model observes a nested record with `tag`, `tag_`, and `()` fields and
an enum containing a field named `tag`. The Rust integration test emits full
and diff logs, checks acceptance, and checks rejection of incorrect record and
enum fields. The method and model both declare the raw parameter `r#type`;
the emitted key `r_type` must match the generated checker, and changing its
value alone must diverge. The Rust method uses the raw spelling `r#set`: its
begin and transition names must both be `t_set`, so a mismatched argument cannot
pass via the checker's unknown-step fallback. It also compares direct and
normalized legacy logs with optional fields omitted. Run it with the pinned
Basis TLC jar, Java, Python and `timeout`:

```sh
TLA2TOOLS_JAR=/absolute/path/to/tla2tools.jar \
  cargo test --manifest-path tla-trace/Cargo.toml --test exporter -- --ignored
```
