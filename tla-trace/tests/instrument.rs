use tla_trace::{Context, Observe, Trace, Value, instrument::trace_step};

#[derive(Observe)]
struct Counter {
    x: u64,
    #[observe(skip)]
    trace: Trace,
}
#[trace_step]
impl Counter {
    fn add(&mut self, amount: u64) -> u64 {
        self.inner(amount);
        self.x
    }
    fn inner(&mut self, amount: u64) {
        self.x += amount;
    }
    fn early(&mut self, fail: bool) -> Result<u64, ()> {
        if fail {
            return Err(());
        }
        self.x += 1;
        Ok(self.x)
    }
    fn panic(&mut self) {
        self.inner(1);
        panic!("inside step");
    }
    #[trace_skip]
    const fn value(&self) -> u64 {
        self.x
    }
}
fn counter(dir: &std::path::Path, id: Option<&str>, diff: bool) -> Counter {
    let mut c = Counter { x: 0, trace: Trace::default() };
    c.trace =
        Trace::object(dir, id, Value::object([("module", Value::from("Counter"))]), diff, |cx| {
            c.observe(cx)
        })
        .unwrap();
    c
}
fn lines(path: &std::path::Path) -> Vec<serde_json::Value> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect()
}
#[test]
fn outermost_early_return_and_diff() {
    let dir = tempfile::tempdir().unwrap();
    let mut c = counter(dir.path(), Some("a"), true);
    assert_eq!(c.add(3), 3);
    assert_eq!(c.early(true), Err(()));
    assert_eq!(c.value(), 3);
    let rows = lines(&dir.path().join("a.ndjson"));
    assert_eq!(rows.len(), 7);
    assert_eq!(rows[0]["state"], serde_json::json!({"x": 0}));
    assert_eq!(rows[1]["step"], "t_add");
    assert_eq!(rows[1]["params"], serde_json::json!({"amount": 3}));
    assert_eq!(rows[2]["diff"], serde_json::json!({"x": 3}));
    assert_eq!(rows[5]["diff"], serde_json::json!({}));
}
#[test]
fn panic_leaves_begin_and_releases_reservation() {
    let dir = tempfile::tempdir().unwrap();
    let mut c = counter(dir.path(), Some("panic"), false);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c.panic())).is_err());
    c.add(2);
    let rows = lines(&dir.path().join("panic.ndjson"));
    assert_eq!(rows.len(), 5);
    assert_eq!(rows[1]["begin"], 1);
    assert_eq!(rows[2]["begin"], 2);
    assert_eq!(rows[3]["state"]["x"], 3);
}
#[test]
fn objects_move_between_threads_without_changing_logs() {
    let dir = tempfile::tempdir().unwrap();
    let a = counter(dir.path(), Some("a"), false);
    let mut b = counter(dir.path(), Some("b"), false);
    std::thread::spawn(move || {
        let mut a = a;
        a.add(5);
    })
    .join()
    .unwrap();
    b.add(7);
    assert_eq!(lines(&dir.path().join("a.ndjson"))[2]["state"]["x"], 5);
    assert_eq!(lines(&dir.path().join("b.ndjson"))[2]["state"]["x"], 7);
    let _ = counter(dir.path(), None, false);
    let _ = counter(dir.path(), None, false);
    assert_eq!(std::fs::read_dir(dir.path()).unwrap().count(), 4);
    assert!(
        Trace::object(dir.path(), Some("a"), Value::object::<&str>([]), false, |_| Value::Null)
            .is_err()
    );
}
#[test]
fn disabled_does_not_observe() {
    struct Disabled {
        trace: Trace,
    }
    impl Disabled {
        #[trace_step(state = panic!("observed disabled state"), params = panic!("observed disabled params"))]
        fn go(&mut self) -> u64 {
            42
        }
    }
    assert_eq!(Disabled { trace: Trace::default() }.go(), 42);
}
#[test]
fn cross_object_nesting_is_not_suppressed() {
    struct Pair {
        trace: Trace,
        other: Counter,
    }
    impl Pair {
        #[trace_step(params = Value::object::<&str>([]), state = Value::object::<&str>([]))]
        fn go(&mut self) {
            self.other.add(1);
        }
    }
    let dir = tempfile::tempdir().unwrap();
    let mut pair = Pair {
        trace: counter(dir.path(), Some("a"), false).trace,
        other: counter(dir.path(), Some("b"), false),
    };
    pair.go();
    assert_eq!(lines(&dir.path().join("a.ndjson")).len(), 4);
    assert_eq!(lines(&dir.path().join("b.ndjson")).len(), 4);
}
#[test]
fn shared_handle_serializes_threads() {
    let dir = tempfile::tempdir().unwrap();
    let trace = counter(dir.path(), Some("shared"), false).trace;
    std::thread::scope(|scope| {
        for _ in 0..4 {
            let trace = trace.clone();
            scope.spawn(move || {
                for _ in 0..10 {
                    let guard = trace.enter("t_inc", |_| Value::object::<&str>([]));
                    std::thread::yield_now();
                    guard.complete(|_| Value::object::<&str>([]));
                }
            });
        }
    });
    let rows = lines(&dir.path().join("shared.ndjson"));
    assert_eq!(rows.len(), 121);
    for (i, chunk) in rows[1..].chunks(3).enumerate() {
        assert_eq!(chunk[0]["begin"], i + 1);
        assert_eq!(chunk[2]["end"], i + 1);
    }
}
#[derive(Clone, Eq, PartialEq)]
struct Opaque(String);
#[derive(Observe)]
struct Generic<T> {
    values: Vec<T>,
    optional: Option<T>,
    #[observe(rename = "label")]
    name: String,
}
#[derive(Observe)]
enum Choice {
    None,
    Tuple(u64, bool),
    Named { value: u64 },
}
#[test]
fn derive_interns_by_equality_and_encodes_variants() {
    let mut cx = Context::default();
    let s = Generic {
        values: vec![Opaque("a".into()), Opaque("b".into()), Opaque("a".into())],
        optional: Some(Opaque("b".into())),
        name: "n".into(),
    };
    assert_eq!(
        s.observe(&mut cx).to_json(),
        r#"{"values": [1, 2, 1], "optional": {"tag": "Some", "v0": 2}, "label": "n"}"#
    );
    assert_eq!(Choice::None.observe(&mut cx), Value::tag("None"));
    assert_eq!(
        Choice::Tuple(1, true).observe(&mut cx).to_json(),
        r#"{"tag": "Tuple", "v0": 1, "v1": true}"#
    );
    assert_eq!(
        Choice::Named { value: 2 }.observe(&mut cx).to_json(),
        r#"{"tag": "Named", "value": 2}"#
    );
}
#[test]
fn collection_encoding() {
    use std::collections::{BTreeMap, BTreeSet};
    let mut cx = Context::default();
    assert_eq!(BTreeSet::from([2u64, 1]).observe(&mut cx).to_json(), "[1, 2]");
    assert_eq!(
        BTreeMap::from([(1u64, Some(2u64))]).observe(&mut cx).to_json(),
        r#"[[1, {"tag": "Some", "v0": 2}]]"#
    );
    assert_eq!([true, false].observe(&mut cx).to_json(), "[true, false]");
}

#[test]
fn impl_keeps_cfg_and_method_override() {
    #[derive(Observe)]
    struct Configured {
        n: u64,
        #[observe(skip)]
        trace: Trace,
    }
    #[trace_step]
    impl Configured {
        /// The active definition keeps this doc comment.
        #[cfg(not(any()))]
        fn go(&mut self) {
            self.n += 1;
        }
        #[cfg(any())]
        fn go(&mut self) {
            compile_error!("inactive method compiled");
        }
        #[trace_step(step = "t_custom")]
        fn custom(&mut self) {
            self.n += 2;
        }
    }
    let dir = tempfile::tempdir().unwrap();
    let mut c = Configured { n: 0, trace: Trace::default() };
    c.trace = Trace::object(dir.path(), Some("cfg"), Value::object::<&str>([]), false, |cx| {
        c.observe(cx)
    })
    .unwrap();
    c.go();
    c.custom();
    let rows = lines(&dir.path().join("cfg.ndjson"));
    assert_eq!(rows.len(), 7);
    assert_eq!(rows[4]["step"], "t_custom");
}

#[test]
fn diff_removes_fields_that_become_unobserved() {
    let dir = tempfile::tempdir().unwrap();
    let trace = Trace::object(dir.path(), Some("remove"), Value::object::<&str>([]), true, |_| {
        Value::object([("a", Value::from(1u64)), ("b", Value::from(2u64))])
    })
    .unwrap();
    trace
        .enter("t_hide", |_| Value::object::<&str>([]))
        .complete(|_| Value::object([("a", Value::from(1u64))]));
    let rows = lines(&dir.path().join("remove.ndjson"));
    assert_eq!(rows[2]["diff"], serde_json::json!({}));
    assert_eq!(rows[2]["remove"], serde_json::json!(["b"]));
}
