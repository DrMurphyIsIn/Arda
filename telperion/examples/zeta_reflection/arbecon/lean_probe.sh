#!/bin/bash
# Run the zeta_reflection island's Lean (v4.32.0) on a Probes module with an out-of-tree olean dir,
# so Probes modules can import each other WITHOUT adding lean_libs to the shared lakefile.
# usage (cwd = telperion/examples/zeta_reflection/lean):  ../arbecon/lean_probe.sh [lean args] File.lean
# env: ARBECON_OLEAN (default ../arbecon/olean).  Heavy runs: wrap in the session's leanlock.sh.
# conjecture1_proved = False.
OLEAN=${ARBECON_OLEAN:-$(cd "$(dirname "$0")" && pwd)/olean}
mkdir -p "$OLEAN/Probes"
export LEAN_PATH="$(lake env printenv LEAN_PATH):$OLEAN"
exec "$(lake env which lean)" "$@"
