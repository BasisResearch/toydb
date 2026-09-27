#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
#
# The per-conjunct inductiveness probes of RaftExportCti.tla, one TLC run
# per inv_* conjunct (seeded with CtiInit_<conjunct>, checking that conjunct)
# and one for the whole invariant, plus inv_ack_persist_dom (see
# RaftExportCti.tla): a summary line each. JAR names the TLA+
# tools; configurations, logs and TLC state go to a temporary directory.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
jar=${JAR:?set JAR to tla2tools.jar}
work=$(mktemp -d)
cd "$here"
all="inv_wf inv_hosts inv_msgs inv_lterms inv_ack_persist inv_vote_persist inv_commits"
all="$all inv_leader_completeness inv_commit_msgs inv_host_commits inv_commit_leaders inv_reads"
for c in wf hosts msgs lterms ack_persist ack_persist_dom vote_persist commits \
         leader_completeness commit_msgs host_commits commit_leaders reads all; do
    inv=inv_$c
    [ "$c" = all ] && inv=$all
    init=CtiInit_${c%_dom}
    sed -e "s/^INIT .*/INIT $init/" -e "s/^INVARIANTS .*/INVARIANTS $inv/" \
        RaftExportCti.cfg > "$work/cti_$c.cfg"
    java -XX:+UseParallelGC -cp "$jar" tlc2.TLC -workers 4 -deadlock -continue \
        -metadir "$work/st_$c" -config "$work/cti_$c.cfg" RaftExportCti.tla \
        > "$work/cti_$c.log" 2>&1 || true
    seed=$(grep -oE 'Finished computing initial states: [0-9]+' "$work/cti_$c.log" | grep -oE '[0-9]+$')
    ctis=$(grep -c 'is violated' "$work/cti_$c.log" || true)
    errs=$(grep -c '^Error: Evaluating invariant' "$work/cti_$c.log" || true)
    echo "$c: seed $seed, $ctis CTIs, $errs evaluation errors ($work/cti_$c.log)"
done
