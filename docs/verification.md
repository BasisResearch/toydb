# Formal verification (Verus)

toyDB opts selected modules into [Verus](https://github.com/verus-lang/verus)
verification. Verus is external-by-default: code outside a `verus!` block is
ignored, so almost all of toyDB compiles and runs unchanged, and only the
opted-in cores are checked. The source of truth for *what* is verified is the
`VERIFY_MODULES` list in [`scripts/verus/verify.sh`](../scripts/verus/verify.sh)
(the `verus-gate` CI job runs exactly that script); this document explains
*which properties* those modules prove and *why the rest of the system is not
yet verified*.

Run it locally with `cargo-verus` on `PATH`:

```
export PATH="$HOME/.local/verus/verus-<arch>:$PATH"
bash scripts/verus/verify.sh
```

## What is proven

### `encoding::keycode` — the order-preserving key encoding

Keycode is the binary encoding for all storage-engine keys. Its two load-bearing
guarantees are **round-trip** (a key decodes back to what was encoded) and
**order preservation** (unsigned byte order of encoded keys matches the logical
order of the values), which is what makes ordered range scans correct. Each
verified spec function has an executable encoder/decoder proven to compute it,
and the real serde `Serializer`/`Deserializer` impls call those verified cores,
so the proofs cover the code that actually runs.

| Property | Statement |
| --- | --- |
| `i64` key round-trip | flipping the sign bit twice is the identity |
| `i64` key order | `a <= b  <==>  i64_key(a) <= i64_key(b)` (unsigned) |
| `f64` key round-trip | `f64_unkey(f64_key(bits)) == bits` for every bit pattern (NaN payloads included) |
| `bool` key | `encode`/`decode` pinned to the `1=true / 0=false` convention |
| byte-string round-trip | `bytes_dec(bytes_enc(v) + suffix) == (v, suffix)` — the `0x00 -> 0x00ff` escape with `0x0000` terminator decodes unambiguously and leaves trailing bytes untouched |
| byte-string encoder/decoder | `encode_bytes` computes `bytes_enc`; `decode_bytes` computes `bytes_dec` (loop-invariant proofs), wired into `serialize_bytes` / `decode_next_bytes` |
| prefix-range coverage | `prefix_range(p)` yields `[p, end)` containing **exactly** the keys prefixed by `p`, under lexicographic byte order — the correctness of SQL table scans and Raft log tail scans |

### `sql::types::value` — integer arithmetic overflow-safety

SQL integer arithmetic must never silently wrap. `checked_add_i64`,
`checked_sub_i64`, and `checked_mul_i64` are proven to return `Some(exact
mathematical result)` precisely when it fits in an `i64` and `None` precisely on
overflow (via a wide `i128` intermediate, with a nonlinear-arith lemma bounding
the product). `Value::checked_add` / `_sub` / `_mul` call them on the
`Integer`/`Integer` path.

## The blocker: why the rest is not (yet) verified

Verus verifies pure, self-contained integer/bit/sequence logic well. The
majority of toyDB lies outside that fragment, and the boundaries below are
fundamental rather than a matter of effort on the current increments:

- **Floating point.** Verus does not model `f64` arithmetic or `f64::total_cmp`.
  This blocks `Value`'s float arithmetic and its mixed-type `Ord` (total order),
  as well as `Status::garbage_disk_percent`.
- **std byte plumbing.** `u64::to_be_bytes` / `from_be_bytes` are unsupported
  (verified experimentally: they require a *trusted* `assume_specification`
  axiom, which would weaken rather than establish the guarantee). The keycode
  *transforms* are verified; the big-endian byte marshalling around them is not.
- **Trait objects and generics.** `dyn storage::Engine`, `ScanIterator`, and the
  generic serde traits are central to the storage engines, the Raft node, and
  MVCC transactions. Verus's support here is limited, and the effectful methods
  (disk, network) are outside its scope.
- **External crates.** `serde`, `bincode`, `BTreeMap`/`BTreeSet`, `crossbeam`,
  and `std::fs`/`std::net` are opaque to Verus.
- **Distributed safety (Raft).** Global properties (election safety, log
  matching, state-machine safety) would require formalizing Raft as a verified
  state machine (e.g. Verus's `state_machines_macros`). That is a large,
  separate formalization effort, and connecting it to the executable
  trait-object-based `raft::node` implementation is itself an open problem.

Progress is therefore made by extracting and verifying pure cores and wiring the
runnable code to call them (as done for keycode and integer arithmetic), rather
than by annotating the effectful, trait-heavy, floating-point majority in place.
