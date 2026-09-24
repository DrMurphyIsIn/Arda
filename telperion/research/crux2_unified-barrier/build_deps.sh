#!/bin/bash
# Prerequisite for checking Crux/Crux2_unified_barrier.lean on the li_positivity island.
#
# Crux2_unified_barrier imports three round-1 research modules that are NOT lean_lib targets of the
# island's lakefile (so `lake build` never compiles them):
#   Crux.Crux_meta_barriers     (Build B: golden fake, Xi, pole shadow)
#   Crux.Crux_dynamics_ergodic  (Build C: ChannelAxioms, channelAxioms_xi)
#   Crux.Crux_axiso_theorem     (class-P collapse classP_eq_zeta, IsDirExp)
# Each of them imports only Mathlib and modules that `lake build` already produces, so we compile
# them with the island's own toolchain straight into the island's build tree, where
# `lake env lean` finds them. Each olean is written to a temporary name and renamed into place
# (atomic on one filesystem), so a concurrent reader never sees a partial file.
# Nothing tracked by git is modified. conjecture1_proved = False.
set -e
ISLAND=${ISLAND:-/Users/peterwmurphy/arda-crux2/telperion/examples/li_positivity/lean}
LOCK=${LEANLOCK:-/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/leanlock.sh}
LOGDIR=${LOGDIR:-$(cd "$(dirname "$0")" && pwd)/outputs}
mkdir -p "$LOGDIR"
cd "$ISLAND"
OUT=.lake/build/lib/lean/Crux
mkdir -p "$OUT"
for M in Crux_meta_barriers Crux_dynamics_ergodic Crux_axiso_theorem; do
  echo "== $M start $(date +%T)"
  TMP="$OUT/.tmp_$$_$M.olean"
  if $LOCK lake env lean -R . -o "$TMP" "Crux/$M.lean" > "$LOGDIR/build_$M.log" 2>&1; then
    mv -f "$TMP" "$OUT/$M.olean"
    echo "== $M OK $(date +%T); axiom lines: $(grep -c 'depends on axioms' "$LOGDIR/build_$M.log"); sorryAx: $(grep -c sorryAx "$LOGDIR/build_$M.log" || true)"
  else
    rm -f "$TMP"
    echo "== $M FAILED (see $LOGDIR/build_$M.log)"; exit 1
  fi
done
