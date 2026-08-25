// SPDX-License-Identifier: MIT
// Sample crate fixture for extract_graph static-fallback tests.
pub mod math;

pub struct Config {
    pub scale: u64,
}

pub fn run(cfg: Config) -> u64 {
    math::add(cfg.scale, 1)
}

mod internal {
    pub fn helper() -> u64 {
        42
    }
}
