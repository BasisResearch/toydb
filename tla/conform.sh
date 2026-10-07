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
#   TLA2TOOLS_JAR=/path/to/tla2tools.jar tla/conform.sh [script | log.ndjson ...]
#
# A script name checks that goldenscript's log (all of them when none is
# given); a path to a .ndjson log checks that log as it is, without running
# the tests. A log whose header has "expect_divergence": <step> must diverge
# at exactly that step (the fixtures in tla/traces/, which keep the trace
# spec able to reject a log).
#
# The jar needs the Json module (the BasisResearch/tlaplus fork's has it).
# verus-tools-mcp's tlc_conform runs the same check from an agent, and on a
# divergence also reports the model's state there and its enabled steps.

set -euo pipefail
cd "$(dirname "$0")/.."
: "${TLA2TOOLS_JAR:?set TLA2TOOLS_JAR to a tla2tools.jar with the Json module}"

logs=target/tla-traces/node
is_path() { [[ "$1" == */* || "$1" == *.ndjson ]]; }

need_tests=$(($# == 0))
for a in "$@"; do is_path "$a" || need_tests=1; done
if [ "$need_tests" = 1 ]; then
  rm -rf "$logs"
  env -u TOYDB_TLA_TRACE_DIR cargo test --quiet --features tla-trace --lib raft::node::tests >/dev/null
fi

files=()
if [ $# -eq 0 ]; then
  files=("$logs"/*.ndjson)
fi
for a in "$@"; do
  if is_path "$a"; then files+=("$a"); else files+=("$logs/$a.ndjson"); fi
done

work=$(mktemp -d)
trap 'rm -rf "$work" tla/Raft_trace_run_$$.cfg' EXIT
failed=0
for f in "${files[@]}"; do
  s=$(basename "$f" .ndjson)
  if [ ! -f "$f" ]; then
    echo "$s: no log at $f"; failed=1; continue
  fi
  log="$(cd "$(dirname "$f")" && pwd)/$(basename "$f")"
  if ! python3 tla-trace/normalize.py "$log" "$work/$s.ndjson"; then
    echo "$s: incomplete or invalid trace"; failed=1; continue
  fi
  log="$work/$s.ndjson"
  steps=$(($(grep -c '' "$log") - 1))
  header=$(head -1 "$log")
  nodes=$(sed -E 's/.*"nodes": ([0-9]+).*/\1/' <<<"$header")
  expect=$(sed -nE 's/.*"expect_divergence": ([0-9]+).*/\1/p' <<<"$header")
  sed -e "s/N = 3/N = $nodes/" -e "s#TraceLog = .*#TraceLog = \"$log\"#" \
    tla/Raft_trace.cfg >"tla/Raft_trace_run_$$.cfg"
  out=$(cd tla && timeout "${TLC_TIMEOUT:-120}s" java -XX:+UseParallelGC -cp "$TLA2TOOLS_JAR" tlc2.TLC -workers 1 \
    -metadir "$work/$s" -config "Raft_trace_run_$$.cfg" Raft_trace.tla 2>&1 || true)
  depth=$(sed -nE 's/.*depth of the complete state graph search is ([0-9]+).*/\1/p' <<<"$out")
  if grep -q '^Error' <<<"$out"; then
    echo "$s: error"; grep -m3 '^Error\|Assert' <<<"$out" | sed 's/^/  /'; failed=1
  elif [ -z "$depth" ]; then
    echo "$s: TLC did not finish"; tail -5 <<<"$out" | sed 's/^/  /'; failed=1
  elif [ "$depth" = $((steps + 1)) ]; then
    if [ -n "$expect" ]; then
      echo "$s: conforms ($steps steps), but should diverge at step $expect"; failed=1
    else
      echo "$s: conforms ($steps steps)"
    fi
  elif [ -n "$expect" ] && [ "$depth" = "$expect" ]; then
    echo "$s: diverges at step $depth of $steps, as expected"
  else
    echo "$s: diverges at step $depth of $steps: $(sed -n "$((depth + 1))p" "$log")"
    failed=1
  fi
done
exit $failed
