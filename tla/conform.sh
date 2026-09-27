#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research.
#
# Trace validation: run the Raft node goldenscripts with every model step
# logged (cargo test --features tla-trace), then check each log against
# Raft.tla with TLC through Raft_trace.tla. A log conforms when TLC's search
# depth is its number of steps plus one; otherwise the depth is the first
# step no behaviour of the model explaining the log can take.
#
#   TLA2TOOLS_JAR=/path/to/tla2tools.jar tla/conform.sh [script ...]
#
# The jar needs the Json module (the BasisResearch/tlaplus fork's has it).
# verus-tools-mcp's tlc_conform runs the same check from an agent, and on a
# divergence also reports the model's state there and its enabled steps.

set -euo pipefail
cd "$(dirname "$0")/.."
: "${TLA2TOOLS_JAR:?set TLA2TOOLS_JAR to a tla2tools.jar with the Json module}"

logs=target/tla-traces/node
cargo test --quiet --features tla-trace --lib raft::node::tests >/dev/null
scripts=("$@")
if [ ${#scripts[@]} -eq 0 ]; then
  for f in "$logs"/*.ndjson; do scripts+=("$(basename "$f" .ndjson)"); done
fi

work=$(mktemp -d)
trap 'rm -rf "$work" tla/Raft_trace_run_$$.cfg' EXIT
failed=0
for s in "${scripts[@]}"; do
  log="$PWD/$logs/$s.ndjson"
  steps=$(($(grep -c '' "$log") - 1))
  nodes=$(head -1 "$log" | sed -E 's/.*"nodes": ([0-9]+).*/\1/')
  sed -e "s/N = 3/N = $nodes/" -e "s#TraceLog = .*#TraceLog = \"$log\"#" \
    tla/Raft_trace.cfg >"tla/Raft_trace_run_$$.cfg"
  out=$(cd tla && java -XX:+UseParallelGC -cp "$TLA2TOOLS_JAR" tlc2.TLC -workers 1 \
    -metadir "$work/$s" -config "Raft_trace_run_$$.cfg" Raft_trace.tla 2>&1 || true)
  depth=$(sed -nE 's/.*depth of the complete state graph search is ([0-9]+).*/\1/p' <<<"$out")
  if grep -q '^Error' <<<"$out"; then
    echo "$s: error"; grep -m3 '^Error\|Assert' <<<"$out" | sed 's/^/  /'; failed=1
  elif [ "$depth" = $((steps + 1)) ]; then
    echo "$s: conforms ($steps steps)"
  else
    echo "$s: diverges at step $depth of $steps: $(sed -n "$((depth + 1))p" "$log")"
    failed=1
  fi
done
exit $failed
