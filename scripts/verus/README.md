# Verus CI

- `verus-gate` verifies the opted-in modules with official upstream Verus in
  a `solver: [z3, cvc5]` matrix. Both jobs must pass; a failure does not cancel
  the other solver. Each job uses a fresh Cargo target directory.
- `verus-verify` runs the Basis fork for verification telemetry and graphs.
  It collects diagnostics after setup or verification errors, then fails the
  job. Dashboard upload failures remain non-fatal.
- `verus-coverage` uses the Basis fork's reachability instrumentation and
  `verus-reach`. Fork results do not replace the upstream proof checks.

`pins.env` pins the official upstream release, its archive SHA-256 and matching
`vstd` version, plus the official cvc5 release and archive SHA-256. Z3 comes
from the upstream Verus archive. Setup rejects `Cargo.lock` mismatches. Update
the upstream release and `vstd` pins together when upgrading.
The cvc5 version follows `source/tools/get-cvc5.sh` at the upstream release.
The pinned upstream Verus release gives cvc5 one cumulative process-wide
resource limit, which is exhausted across toyDB's many proof queries. The
upstream setup routes the official cvc5 binary through
`cvc5-per-check-rlimit.sh`, translating that option to cvc5's equivalent
per-query limit while preserving the solver binary and all other arguments.

The Basis installer resolves `VERUS_REF` and installs both solver builds
specified by that release's `version.json`. `VERUS_MCP_REF` is only for the
local agent launcher; CI does not run an MCP server and reports a null MCP
version in telemetry.

Setup and failure-reporting regression tests run without a verifier, solver,
network connection, or Rust installation:

```sh
python3 scripts/verus/test_setup.py
python3 scripts/verus/test_extract.py
```
