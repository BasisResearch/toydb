// SPDX-License-Identifier: MIT
// Sample crate fixture module for extract_graph static-fallback tests.

pub fn add(a: u64, b: u64) -> u64 {
    a + b
}

pub fn mul(a: u64, b: u64) -> u64 {
    a * b
}

pub trait Number {
    fn zero() -> Self;
}

impl Number for u64 {
    fn zero() -> Self {
        0
    }
}
