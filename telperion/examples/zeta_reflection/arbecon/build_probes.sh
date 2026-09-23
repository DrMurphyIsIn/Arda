#!/bin/bash
# Compile the ArbEconomics probes in dependency order and run the axiom guard.
# usage (cwd = telperion/examples/zeta_reflection/lean):  ../arbecon/build_probes.sh [TAG ...]
#   default TAGs: T100 T1000 T10000 T30000 (their modules must exist in Probes/, see gen_height.py)
# Prefix every heavy Lean call with $LOCK (e.g. LOCK=/path/leanlock.sh) to respect machine-wide slots.
# conjecture1_proved = False.
set -e
H=$(cd "$(dirname "$0")" && pwd)
L="$LOCK $H/lean_probe.sh"
OLEAN=${ARBECON_OLEAN:-$H/olean}
c() { echo "== $1"; /usr/bin/time -l $L -Dprofiler=true -Dprofiler.threshold=100 -o "$OLEAN/Probes/$1.olean" "Probes/$1.lean" 2>&1 \
        | grep -E "error|type checking took|maximum resident| real" || true; }
for m in ArbEconomics_Eval ArbEconomics_Sound ArbEconomics_Zeta; do c $m; done
TAGS=${@:-T100 T1000 T10000 T30000}
for T in $TAGS; do
  c ArbEconomics_${T}_Cfg
  for p in $(ls Probes/ArbEconomics_${T}_P*.lean | sed 's|Probes/||; s|\.lean$||' | sort -V); do c $p; done
  c ArbEconomics_$T
done
[ -z "$NOGUARD" ] && c ArbEconomics_Guard
