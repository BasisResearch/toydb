#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
#
# The oracle columns of EXPORT.md, from ../Raft.tla and ../Raft_cti.tla.
#
#   oracle.sh a3     the oracle as committed: the CTI probe loop
#   oracle.sh noa3   the oracle with its four `\* bound, see (A3)` guard lines
#                    deleted: Raft_noA3.cfg and Raft_deep_lc_noA3.cfg (the
#                    oracle's configurations without TypeOK, which the
#                    guard-free successors past the bound leave), then the
#                    CTI probe loop
#
# The CTI loop is cti.sh's, on Raft_cti.tla: one TLC run per inv_* conjunct
# (seeded with CtiInit_<conjunct>, checking that conjunct), one for the
# whole invariant, and inv_ack_persist_dom (seeded with CtiInit_ack_persist).
# JAR names the TLA+ tools; the modules, configurations, logs and TLC state
# go to a temporary directory, printed at the end.
set -euo pipefail
mode=${1:?usage: oracle.sh a3|noa3}
here=$(cd "$(dirname "$0")" && pwd)
jar=${JAR:?set JAR to tla2tools.jar}
work=$(mktemp -d)
cp "$here/../Raft.tla" "$here/../Raft_cti.tla" "$work/"
case $mode in
    a3) ;;
    noa3)
        guards=$(grep -c 'bound, see (A3)' "$work/Raft.tla")
        [ "$guards" = 4 ] || { echo "expected 4 (A3) guard lines, found $guards" >&2; exit 1; }
        sed -i '/bound, see (A3)/d' "$work/Raft.tla"
        cp "$here/Raft_noA3.cfg" "$here/Raft_deep_lc_noA3.cfg" "$work/"
        cd "$work"
        for c in Raft_noA3 Raft_deep_lc_noA3; do
            java -XX:+UseParallelGC -cp "$jar" tlc2.TLC -workers 4 -continue \
                -metadir "$work/st_$c" -config "$c.cfg" Raft.tla > "$work/$c.log" 2>&1 || true
            gen=$(grep -oE '^[0-9]+ states generated, [0-9]+ distinct' "$work/$c.log" || echo 'no result')
            viol=$(grep -c 'is violated' "$work/$c.log" || true)
            echo "$c: $gen, $viol violations ($work/$c.log)"
        done
        ;;
    *) echo "usage: oracle.sh a3|noa3" >&2; exit 1 ;;
esac
cd "$work"
consts=$(sed -n '/^CONSTANTS/,/^$/p' "$here/../Raft_cti_small.cfg")
all="inv_wf inv_hosts inv_msgs inv_lterms inv_ack_persist inv_vote_persist inv_commits"
all="$all inv_leader_completeness inv_commit_msgs inv_host_commits inv_commit_leaders inv_reads"
for c in wf hosts msgs lterms ack_persist ack_persist_dom vote_persist commits \
         leader_completeness commit_msgs host_commits commit_leaders reads all; do
    inv=inv_$c
    [ "$c" = all ] && inv=$all
    printf '%s\nINIT CtiInit_%s\nNEXT Next\nCONSTRAINT CtiOneStep\nINVARIANTS %s\n' \
        "$consts" "${c%_dom}" "$inv" > "cti_$c.cfg"
    java -XX:+UseParallelGC -cp "$jar" tlc2.TLC -workers 4 -deadlock -continue \
        -metadir "$work/st_$c" -config "cti_$c.cfg" Raft_cti.tla > "cti_$c.log" 2>&1 || true
    seed=$(grep -oE 'Finished computing initial states: [0-9]+' "cti_$c.log" | grep -oE '[0-9]+$')
    ctis=$(grep -c 'is violated' "cti_$c.log" || true)
    errs=$(grep -c '^Error: Evaluating invariant' "cti_$c.log" || true)
    echo "$c: seed $seed, $ctis CTIs, $errs evaluation errors ($work/cti_$c.log)"
done
