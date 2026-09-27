#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
#
# Regenerate GState_tla.{tla,cfg,tla.json} from src/raft/safety.rs with
# Verus's TLA+ exporter (`-V tla-export`, BasisResearch/verus). VERUS names
# the verus binary (default: `verus` on PATH); a source build also needs
# VERUS_MCP_ENABLED=1 in the environment. The twelve inv_* conjuncts are
# named so each is checked on its own (unnamed, only `inv`, which calls them
# all, would be). Verus empties its --log-dir, so the export goes to a
# temporary directory and only its three files are copied here.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
log=$(mktemp -d)
trap 'rm -rf "$log"' EXIT
invs=inv_wf,inv_hosts,inv_msgs,inv_lterms,inv_ack_persist,inv_vote_persist,inv_commits
invs=$invs,inv_leader_completeness,inv_commit_msgs,inv_host_commits,inv_commit_leaders,inv_reads
cd "$root"
"${VERUS:-verus}" src/raft/safety.rs --crate-type=lib --no-verify \
    -V "tla-export=safety:$invs" --log-dir "$log"
cp "$log/GState_tla.tla" "$log/GState_tla.cfg" "$log/GState_tla.tla.json" "$here/"
