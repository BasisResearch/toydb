use std::path::Path;
use std::process::Command;
use tla_trace::{Context, Observe, Trace, Value, instrument::trace_step};

#[derive(Observe)]
struct Record {
    tag: u64,
    tag_: u64,
    unit: (),
}
#[derive(Observe)]
enum Choice {
    A { tag: u64 },
    B,
}
#[derive(Observe)]
struct State {
    record: Record,
    choice: Choice,
    #[observe(skip)]
    trace: Trace,
}
impl State {
    #[trace_step]
    fn set(&mut self, n: u64) {
        self.record.tag = n;
        self.choice = Choice::A { tag: n };
    }
}

#[test]
fn reserved_names_and_unit_keep_their_distinct_encodings() {
    let mut cx = Context::default();
    assert_eq!(
        Record { tag: 1, tag_: 7, unit: () }.observe(&mut cx).to_json(),
        r#"{"tag_": 1, "tag__": 7, "unit": []}"#,
    );
    assert_eq!(Choice::A { tag: 1 }.observe(&mut cx).to_json(), r#"{"tag": "A", "tag_": 1}"#,);
    assert_eq!(Choice::B.observe(&mut cx), Value::tag("B"));
    #[derive(Observe)]
    struct Empty {}
    assert_eq!(Empty {}.observe(&mut cx).to_json(), "{}");
}

fn write_rows(path: &Path, rows: &[serde_json::Value]) {
    let text = rows.iter().map(|r| format!("{r}\n")).collect::<String>();
    std::fs::write(path, text).unwrap();
}

fn check_depth(work: &Path, log: &Path, expected: usize) {
    std::fs::write(
        work.join("trace.cfg"),
        format!(
            "CONSTANT TraceLog = {}\nINIT TraceInit\nNEXT TraceNext\nCHECK_DEADLOCK FALSE\n",
            serde_json::to_string(log.to_str().unwrap()).unwrap(),
        ),
    )
    .unwrap();
    let output = Command::new("timeout")
        .arg("30s")
        .arg("java")
        .arg("-XX:+UseParallelGC")
        .arg("-cp")
        .arg(std::env::var_os("TLA2TOOLS_JAR").expect("set TLA2TOOLS_JAR to the pinned TLC jar"))
        .args(["tlc2.TLC", "-workers", "1", "-config", "trace.cfg", "State_tla_trace"])
        .current_dir(work)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(!stdout.contains("Error:"), "{stdout}");
    assert!(
        stdout.contains(&format!("depth of the complete state graph search is {expected}.")),
        "{}: expected depth {expected}\n{stdout}",
        log.display(),
    );
}

#[test]
#[ignore = "requires Java, timeout, Python, and TLA2TOOLS_JAR; run in the trace CI job"]
fn emitted_and_legacy_logs_conform_to_the_exported_model() {
    let dir = tempfile::tempdir().unwrap();
    let work = dir.path();
    std::fs::write(work.join("State_tla.tla"), include_str!("exporter/State_tla.tla")).unwrap();
    std::fs::write(work.join("State_tla_trace.tla"), include_str!("exporter/State_tla_trace.tla"))
        .unwrap();
    let normalize = Path::new(env!("CARGO_MANIFEST_DIR")).join("normalize.py");
    for diff in [false, true] {
        let id = if diff { "diff" } else { "full" };
        let mut state = State {
            record: Record { tag: 0, tag_: 7, unit: () },
            choice: Choice::A { tag: 0 },
            trace: Trace::default(),
        };
        state.trace = Trace::object(
            work,
            Some(id),
            Value::object([
                ("module", Value::from("State_tla")),
                ("export", Value::from("encoding")),
            ]),
            diff,
            |cx| state.observe(cx),
        )
        .unwrap();
        state.set(1);
        state.set(2);
        drop(state);
        let input = work.join(format!("{id}.ndjson"));
        let normalized = work.join("normalized.ndjson");
        assert!(
            Command::new("python3")
                .arg(&normalize)
                .arg(&input)
                .arg(&normalized)
                .status()
                .unwrap()
                .success()
        );
        check_depth(work, &normalized, 3);
        let rows: Vec<serde_json::Value> = std::fs::read_to_string(&normalized)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        // Incorrect reserved-name fields must cause divergence, not disappear
        // from the observer as they did when encoded as the reserved "tag".
        for field in ["record", "choice"] {
            let mut bad = rows.clone();
            bad[1]["state"][field]["tag_"] = serde_json::json!(99);
            write_rows(&input, &bad);
            check_depth(work, &input, 1);
        }
        // The old checker and normalization must agree for every combination
        // of optional legacy fields, including model-inferred parameters.
        for omit in [vec!["state"], vec!["params"], vec!["state", "params"]] {
            let mut legacy = rows.clone();
            for row in &mut legacy[1..] {
                for key in &omit {
                    row.as_object_mut().unwrap().remove(*key);
                }
            }
            write_rows(&input, &legacy);
            check_depth(work, &input, 3);
            assert!(
                Command::new("python3")
                    .arg(&normalize)
                    .arg(&input)
                    .arg(&normalized)
                    .status()
                    .unwrap()
                    .success()
            );
            check_depth(work, &normalized, 3);
        }
    }
}
