// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Basis Research.

#![doc = include_str!("../README.md")]

use std::cell::RefCell;
use std::fmt::Write as _;
use std::path::Path;

/// A JSON value in the exporter's encoding.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Int(i128),
    Str(String),
    Array(Vec<Value>),
    /// An object, its keys in the order given.
    Object(Vec<(String, Value)>),
}

impl Value {
    /// An object from `(key, value)` pairs.
    pub fn object<K: Into<String>>(fields: impl IntoIterator<Item = (K, Value)>) -> Value {
        Value::Object(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
    }

    /// An enum value of a variant without fields: `{"tag": variant}`.
    pub fn tag(variant: &str) -> Value {
        Value::object([("tag", Value::Str(variant.into()))])
    }

    /// `Option`: `{"tag": "None"}` or `{"tag": "Some", "v0": v}`.
    pub fn option(v: Option<Value>) -> Value {
        match v {
            None => Value::tag("None"),
            Some(v) => Value::object([("tag", Value::Str("Some".into())), ("v0", v)]),
        }
    }

    /// Append this value's JSON text to `out`.
    pub fn write_json(&self, out: &mut String) {
        match self {
            Value::Null => out.push_str("null"),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::Int(i) => {
                let _ = write!(out, "{i}");
            }
            Value::Str(s) => write_str(s, out),
            Value::Array(items) => {
                out.push('[');
                for (n, v) in items.iter().enumerate() {
                    if n > 0 {
                        out.push_str(", ");
                    }
                    v.write_json(out);
                }
                out.push(']');
            }
            Value::Object(fields) => {
                out.push('{');
                for (n, (k, v)) in fields.iter().enumerate() {
                    if n > 0 {
                        out.push_str(", ");
                    }
                    write_str(k, out);
                    out.push_str(": ");
                    v.write_json(out);
                }
                out.push('}');
            }
        }
    }

    pub fn to_json(&self) -> String {
        let mut s = String::new();
        self.write_json(&mut s);
        s
    }
}

fn write_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

macro_rules! from_int {
    ($($t:ty),*) => {$(
        impl From<$t> for Value {
            fn from(i: $t) -> Value {
                Value::Int(i as i128)
            }
        }
    )*};
}
from_int!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

impl From<bool> for Value {
    fn from(b: bool) -> Value {
        Value::Bool(b)
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Value {
        Value::Str(s.into())
    }
}

impl From<String> for Value {
    fn from(s: String) -> Value {
        Value::Str(s)
    }
}

impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(items: Vec<T>) -> Value {
        Value::Array(items.into_iter().map(Into::into).collect())
    }
}

impl<T: Into<Value>> From<Option<T>> for Value {
    fn from(v: Option<T>) -> Value {
        Value::option(v.map(Into::into))
    }
}

mod object;
mod observe;
pub use object::{Event, StepGuard, Trace};
pub use observe::{Context, Observe};
pub use tla_trace_macros::Observe;
/// Attributes have their own path because Rust shares the macro namespace
/// between attributes and function-like macros.
pub mod instrument {
    pub use tla_trace_macros::trace_step;
}

thread_local! {
    static LOG: RefCell<Trace> = RefCell::new(Trace::default());
}
/// Open a compatibility log for this thread, with a v2 header.
pub fn start(path: &Path, header: Value) -> std::io::Result<()> {
    let trace = Trace::at(path, header)?;
    LOG.with(|l| *l.borrow_mut() = trace);
    Ok(())
}
/// Obtain the current thread's handle (disabled when no log is open).
pub fn thread_log() -> Trace {
    LOG.with(|l| l.borrow().clone())
}
pub fn active() -> bool {
    LOG.with(|l| l.borrow().active())
}
pub fn emit(step: &str, params: Value, state: Value) {
    thread_log().emit(Event::new(step, params, state));
}
pub fn finish() {
    LOG.with(|l| *l.borrow_mut() = Trace::default());
}

/// Log one step: `trace_step!("t_grant", {v: 1, c: 0, term: 2}, state)`,
/// the parameters by their names in the model, the observed state a
/// [`Value`]. The state expression is evaluated only when a log is open.
#[macro_export]
macro_rules! trace_step {
    ($step:expr, { $($k:ident : $v:expr),* $(,)? }, $state:expr) => {
        if $crate::active() {
            $crate::emit(
                $step,
                $crate::Value::Object(vec![$((stringify!($k).to_string(), $crate::Value::from($v))),*]),
                $state,
            );
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values_print_in_the_exporter_encoding() {
        let v = Value::object([
            ("term", Value::from(2u64)),
            ("vote", Value::from(Some(1u8))),
            ("role", Value::tag("Leader")),
            ("log", Value::from(vec![3i64, 4])),
            ("s", Value::from("a\"b\n")),
        ]);
        assert_eq!(
            v.to_json(),
            r#"{"term": 2, "vote": {"tag": "Some", "v0": 1}, "role": {"tag": "Leader"}, "log": [3, 4], "s": "a\"b\n"}"#
        );
        assert_eq!(Value::from(None::<u8>).to_json(), r#"{"tag": "None"}"#);
    }

    #[test]
    fn a_log_is_the_header_then_one_line_per_step_of_its_thread() {
        let dir = std::env::temp_dir().join(format!("tla-trace-test-{}", std::process::id()));
        let path = dir.join("t.ndjson");
        trace_step!("t_before", {}, Value::Null);
        start(&path, Value::object([("module", Value::from("M"))])).unwrap();
        assert!(active());
        trace_step!("t_a", { i: 0u8, term: 2u64 }, Value::object([("x", Value::from(1u8))]));
        // Another thread has no log open: its steps go nowhere.
        std::thread::spawn(|| trace_step!("t_elsewhere", {}, Value::Null)).join().unwrap();
        trace_step!("t_b", {}, Value::object::<&str>([]));
        finish();
        assert!(!active());
        trace_step!("t_after", {}, Value::Null);
        let text = std::fs::read_to_string(&path).unwrap();
        assert_eq!(
            text,
            "{\"module\": \"M\", \"format\": \"tla-trace-v2\", \"state\": {}}\n\
             {\"step\": \"t_a\", \"params\": {\"i\": 0, \"term\": 2}, \"state\": {\"x\": 1}}\n\
             {\"step\": \"t_b\", \"params\": {}, \"state\": {}}\n"
        );
        let _ = std::fs::remove_dir_all(dir);
    }
}
