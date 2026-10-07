use crate::{Context, Value};
use std::io::{self, Write};
use std::path::Path;
use std::sync::{
    Arc, Condvar, Mutex,
    atomic::{AtomicU64, Ordering},
};
use std::thread::ThreadId;

static IDS: AtomicU64 = AtomicU64::new(1);

/// An owned identity. Moves retain identity; clones share a log. Give distinct
/// objects distinct handles, even when their data is cloned. Default is disabled.
#[derive(Clone, Default)]
pub struct Trace(Option<Arc<Inner>>);
struct Inner {
    state: Mutex<State>,
    ready: Condvar,
}
struct State {
    file: std::fs::File,
    owner: Option<ThreadId>,
    next: u64,
    cx: Context,
    previous: Value,
    diff: bool,
}
/// One model transition; compound methods may return several, in model order.
pub struct Event {
    pub step: String,
    pub params: Value,
    pub state: Value,
}
impl Event {
    pub fn new(step: &str, params: Value, state: Value) -> Self {
        Self { step: step.into(), params, state }
    }
}
impl Trace {
    /// Create one file per object. Explicit IDs must be unique in this directory;
    /// create_new rejects collisions instead of truncating an earlier instance.
    pub fn object(
        directory: &Path,
        id: Option<&str>,
        header: Value,
        diff: bool,
        initial: impl FnOnce(&mut Context) -> Value,
    ) -> io::Result<Self> {
        let id = id.map(str::to_owned).unwrap_or_else(|| {
            format!("{}-{}", std::process::id(), IDS.fetch_add(1, Ordering::Relaxed))
        });
        if id.is_empty() || !id.bytes().all(|b| b.is_ascii_alphanumeric() || b"-_".contains(&b)) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "trace id must contain only letters, digits, - or _",
            ));
        }
        std::fs::create_dir_all(directory)?;
        let mut cx = Context::default();
        let initial = initial(&mut cx);
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(directory.join(format!("{id}.ndjson")))?;
        Self::open(file, header, initial, cx, diff)
    }
    pub(crate) fn at(path: &Path, header: Value) -> io::Result<Self> {
        if let Some(dir) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
            std::fs::create_dir_all(dir)?;
        }
        let initial = match &header {
            Value::Object(f) => f.iter().find(|(k, _)| k == "state").map(|(_, v)| v.clone()),
            _ => None,
        }
        .unwrap_or_else(|| Value::object::<&str>([]));
        Self::open(std::fs::File::create(path)?, header, initial, Context::default(), false)
    }
    fn open(
        mut file: std::fs::File,
        header: Value,
        initial: Value,
        cx: Context,
        diff: bool,
    ) -> io::Result<Self> {
        let Value::Object(mut fields) = header else {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "header must be a record"));
        };
        fields.retain(|(k, _)| k != "format" && k != "state");
        fields.push(("format".into(), Value::from("tla-trace-v2")));
        fields.push(("state".into(), initial.clone()));
        writeln!(file, "{}", Value::Object(fields).to_json())?;
        file.flush()?;
        Ok(Self(Some(Arc::new(Inner {
            state: Mutex::new(State { file, owner: None, next: 1, cx, previous: initial, diff }),
            ready: Condvar::new(),
        }))))
    }
    pub fn active(&self) -> bool {
        self.0.is_some()
    }
    /// Reserve this object's log through completion. Reentrant calls on this
    /// thread are suppressed; different objects remain independent. Contending
    /// threads wait, so begin/body/completion have one total order per object.
    pub fn enter(&self, step: &str, params: impl FnOnce(&mut Context) -> Value) -> StepGuard {
        let Some(inner) = &self.0 else {
            return StepGuard::disabled();
        };
        let me = std::thread::current().id();
        let mut s = inner.state.lock().unwrap_or_else(|e| e.into_inner());
        if s.owner == Some(me) {
            return StepGuard::disabled();
        }
        while s.owner.is_some() {
            s = inner.ready.wait(s).unwrap_or_else(|e| e.into_inner());
        }
        let params = params(&mut s.cx);
        let id = s.next;
        s.next += 1;
        write_line(
            &mut s,
            Value::object([
                ("begin", Value::from(id)),
                ("step", Value::from(step)),
                ("params", params.clone()),
            ]),
        );
        s.owner = Some(me);
        StepGuard {
            trace: self.clone(),
            id,
            step: step.into(),
            params,
            // A reservation must never migrate to another thread.
            _not_send: std::marker::PhantomData,
        }
    }
    pub(crate) fn emit(&self, event: Event) {
        if let Some(inner) = &self.0 {
            let mut s = inner.state.lock().unwrap_or_else(|e| e.into_inner());
            event_line(&mut s, event);
        }
    }
}
fn write_line(s: &mut State, line: Value) {
    writeln!(s.file, "{}", line.to_json())
        .and_then(|_| s.file.flush())
        .expect("tla-trace: writing log failed");
}
fn event_line(s: &mut State, event: Event) {
    let mut fields = vec![("step", Value::from(event.step)), ("params", event.params)];
    if s.diff {
        if let (Value::Object(old), Value::Object(new)) = (&s.previous, &event.state) {
            let changed = new
                .iter()
                .filter(|(k, v)| old.iter().find(|(key, _)| key == k).map(|(_, v)| v) != Some(v))
                .cloned()
                .collect();
            let removed = old
                .iter()
                .filter(|(k, _)| !new.iter().any(|(key, _)| key == k))
                .map(|(k, _)| Value::from(k.clone()))
                .collect();
            fields.push(("diff", Value::Object(changed)));
            fields.push(("remove", Value::Array(removed)));
        } else {
            panic!("tla-trace: diff mode requires record states");
        }
    } else {
        fields.push(("state", event.state.clone()));
    }
    s.previous = event.state;
    write_line(s, Value::object(fields));
}

/// RAII reservation; dropping without completion leaves an unmatched begin.
#[must_use]
pub struct StepGuard {
    trace: Trace,
    id: u64,
    step: String,
    params: Value,
    _not_send: std::marker::PhantomData<std::rc::Rc<()>>,
}
impl StepGuard {
    fn disabled() -> Self {
        Self {
            trace: Trace::default(),
            id: 0,
            step: String::new(),
            params: Value::Null,
            _not_send: std::marker::PhantomData,
        }
    }
    pub fn is_outer(&self) -> bool {
        self.trace.active()
    }
    pub fn complete(self, observe: impl FnOnce(&mut Context) -> Value) {
        if let Some(inner) = &self.trace.0 {
            let mut s = inner.state.lock().unwrap_or_else(|e| e.into_inner());
            let state = observe(&mut s.cx);
            event_line(&mut s, Event::new(&self.step, self.params.clone(), state));
            write_line(&mut s, Value::object([("end", Value::from(self.id))]));
        }
    }
    pub fn complete_events(self, events: Vec<Event>) {
        if let Some(inner) = &self.trace.0 {
            let mut s = inner.state.lock().unwrap_or_else(|e| e.into_inner());
            for e in events {
                event_line(&mut s, e);
            }
            write_line(&mut s, Value::object([("end", Value::from(self.id))]));
        }
    }
}
impl Drop for StepGuard {
    fn drop(&mut self) {
        if let Some(inner) = &self.trace.0 {
            let mut s = inner.state.lock().unwrap_or_else(|e| e.into_inner());
            // No I/O during unwinding. The durable begin is the failure marker.
            s.owner = None;
            inner.ready.notify_one();
        }
    }
}
