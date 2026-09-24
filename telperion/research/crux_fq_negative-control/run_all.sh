#!/bin/sh
# Re-run every Guinand-Weil / dual-weight check of the negative-control seat, ONE PROCESS AT A TIME
# (no multiprocessing pools: the machine had a memory crunch). Outputs go to out/<script>.out.
cd "$(dirname "$0")"
mkdir -p out
for f in ef_zeta_control ef_dh ef_w1 ef_w2 ef_golden_etheta ef_dual_growth ef_epstein ef_epstein_locate ef_epstein_locate2; do
  echo "== $f (start $(date +%H:%M:%S))"
  /usr/bin/time -p python3 "$f.py" > "out/$f.out" 2> "out/$f.time"
  echo "   exit $? ; $(grep real out/$f.time)"
done
