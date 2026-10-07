use crate::Value;
use std::any::{Any, TypeId};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

/// Stable equality-based names, shared by parameters and state for one log.
/// Values are retained until the log is dropped; padding and addresses are never read.
#[derive(Default)]
pub struct Context {
    values: HashMap<TypeId, Box<dyn Any + Send>>,
}
impl Context {
    pub fn intern<T: Clone + Eq + Send + 'static>(&mut self, value: &T) -> Value {
        let values = self
            .values
            .entry(TypeId::of::<T>())
            .or_insert_with(|| Box::new(Vec::<T>::new()))
            .downcast_mut::<Vec<T>>()
            .unwrap();
        let index = values.iter().position(|v| v == value).unwrap_or_else(|| {
            values.push(value.clone());
            values.len() - 1
        });
        Value::Int((index + 1) as i128)
    }
}

/// Observe a value in the TLA exporter's encoding. Arrays represent sequences
/// (TLA positions 1..Len), sets, tuples, and maps of [key,value] pairs.
pub trait Observe {
    fn observe(&self, cx: &mut Context) -> Value;
}
macro_rules! scalars {
    ($($t:ty),*) => {$(impl Observe for $t {
        fn observe(&self, _: &mut Context) -> Value { Value::from(self.clone()) }
    })*};
}
scalars!(bool, u8, u16, u32, u64, usize, i8, i16, i32, i64, isize, String);
impl Observe for i128 {
    fn observe(&self, _: &mut Context) -> Value {
        Value::Int(*self)
    }
}
impl Observe for str {
    fn observe(&self, _: &mut Context) -> Value {
        Value::from(self)
    }
}
impl Observe for char {
    fn observe(&self, _: &mut Context) -> Value {
        Value::from(self.to_string())
    }
}
impl Observe for Value {
    fn observe(&self, _: &mut Context) -> Value {
        self.clone()
    }
}
impl<T: Observe + ?Sized> Observe for &T {
    fn observe(&self, cx: &mut Context) -> Value {
        (**self).observe(cx)
    }
}
impl<T: Observe + ?Sized> Observe for &mut T {
    fn observe(&self, cx: &mut Context) -> Value {
        (**self).observe(cx)
    }
}
impl<T: Observe + ?Sized> Observe for Box<T> {
    fn observe(&self, cx: &mut Context) -> Value {
        (**self).observe(cx)
    }
}
impl<T: Observe> Observe for Option<T> {
    fn observe(&self, cx: &mut Context) -> Value {
        Value::option(self.as_ref().map(|v| v.observe(cx)))
    }
}
impl<T: Observe> Observe for [T] {
    fn observe(&self, cx: &mut Context) -> Value {
        Value::Array(self.iter().map(|v| v.observe(cx)).collect())
    }
}
impl<T: Observe, const N: usize> Observe for [T; N] {
    fn observe(&self, cx: &mut Context) -> Value {
        self.as_slice().observe(cx)
    }
}
macro_rules! sequences {
    ($($t:ident),*) => {$(impl<T: Observe> Observe for $t<T> {
        fn observe(&self, cx: &mut Context) -> Value { Value::Array(self.iter().map(|v| v.observe(cx)).collect()) }
    })*};
}
sequences!(Vec, VecDeque, BTreeSet);
impl<T: Observe, S> Observe for HashSet<T, S> {
    fn observe(&self, cx: &mut Context) -> Value {
        Value::Array(self.iter().map(|v| v.observe(cx)).collect())
    }
}
impl<K: Observe, V: Observe> Observe for BTreeMap<K, V> {
    fn observe(&self, cx: &mut Context) -> Value {
        Value::Array(
            self.iter().map(|(k, v)| Value::Array(vec![k.observe(cx), v.observe(cx)])).collect(),
        )
    }
}
impl<K: Observe, V: Observe, S> Observe for HashMap<K, V, S> {
    fn observe(&self, cx: &mut Context) -> Value {
        Value::Array(
            self.iter().map(|(k, v)| Value::Array(vec![k.observe(cx), v.observe(cx)])).collect(),
        )
    }
}
impl<A: Observe, B: Observe> Observe for (A, B) {
    fn observe(&self, cx: &mut Context) -> Value {
        Value::Array(vec![self.0.observe(cx), self.1.observe(cx)])
    }
}
impl Observe for () {
    fn observe(&self, _: &mut Context) -> Value {
        Value::Array(vec![])
    }
}
