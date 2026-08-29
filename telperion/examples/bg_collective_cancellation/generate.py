"""The COLLECTIVE-CANCELLATION obstruction, kernel-gated (PROOF_STATUS "ruled out" #1).

Audit finding (2026-08-29, confirms PROOF_STATUS #1): `Phi^11 <= 1` is a genuine collective
cancellation, not a sum of non-positive local terms.  In the per-vertex factorization
`Phi^11(T) = prod_v f_v`, `f_v = (64/621) a_v^11`, the tie N(0,5) has exactly three distinct
factors -- and TWO of them exceed 1:

    leaf (a=1)     : f = 64/621            ~ 0.103   < 1
    hub  (a=23/18) : f = hub_factor(5)     ~ 1.528   > 1   (the +0.424 log-defect)
    arm-mid (a=3/2): f = 6561/736          ~ 8.914   > 1

yet the full product over the 11 vertices (5 leaves + 5 arm-mids + 1 hub) is EXACTLY 1:

    (64/621)^5 * (6561/736)^5 * hub_factor(5)  =  1.

Because per-vertex factors exceed 1, NO decomposition into per-vertex factors that are all
`<= 1` (equivalently, no sum of non-positive local terms) can bound `Phi^11` -- the `<= 1`
arises only collectively.  This is the exact reason local-potential / per-node-monotone
methods fail (the campaign's `+0.199` residual stall).

SCOPE (honest).  Records the collective-cancellation obstruction as exact rational facts
in-kernel; it does NOT prove `Phi^11 <= 1` (the open crux -- which is precisely what no
LOCAL method reaches).  conjecture1_proved = False.

    python3 examples/bg_collective_cancellation/generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.collective_cancellation import per_vertex_factor, hub_factor, near_star_balance  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE / "frozen" / "BGCollectiveCancellation.lean"


def _facts():
    leaf = per_vertex_factor(Fr(1))       # 64/621
    mid = per_vertex_factor(Fr(3, 2))     # 6561/736
    hub = hub_factor(5)                    # per_vertex_factor(23/18)
    assert leaf < 1 and mid > 1 and hub > 1
    assert leaf ** 5 * mid ** 5 * hub == 1 == near_star_balance(5)
    return leaf, mid, hub


def _q(fr: Fr) -> str:
    return f"({fr.numerator} : ℚ) / {fr.denominator}"


def build() -> str:
    leaf, mid, hub = _facts()
    thms = [
        f"-- leaf vertex (a=1): sub-unit factor\ntheorem pvf_leaf_sub_unit : {_q(leaf)} < 1 := by norm_num",
        f"-- hub vertex (a=23/18): factor EXCEEDS 1 (the +0.424 log-defect)\n"
        f"theorem pvf_hub_excess : {_q(hub)} > 1 := by norm_num",
        f"-- arm-mid vertex (a=3/2): factor EXCEEDS 1\ntheorem pvf_armmid_excess : {_q(mid)} > 1 := by norm_num",
        f"-- the tie N(0,5): full per-vertex factorization (5 leaves, 5 arm-mids, 1 hub) = 1 exactly\n"
        f"theorem tie_collective_balance :\n"
        f"    ({_q(leaf)}) ^ 5 * ({_q(mid)}) ^ 5 * ({_q(hub)}) = 1 := by norm_num",
    ]
    header = (
        "/- The COLLECTIVE-CANCELLATION obstruction, kernel-gated (PROOF_STATUS \"ruled out\" #1).\n"
        "   Per-vertex factorization Phi^11 = prod_v (64/621)a_v^11.  The tie N(0,5) has TWO of its\n"
        "   three distinct factors > 1 (hub ~1.528, arm-mid ~8.914) yet the full product = 1 --\n"
        "   so no all-<=1 per-vertex decomposition (no sum of non-positive local terms) can bound\n"
        "   Phi^11; the <=1 is collective.  Records the obstruction; does NOT prove the crux.\n"
        "   conjecture1_proved = False. -/\n"
        "import Mathlib\n\nnamespace BGCollectiveCancellation\n\n"
    )
    return header + "\n\n".join(thms) + "\n\nend BGCollectiveCancellation\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        if not OUT.exists():
            print(f"MISSING: {OUT}")
            return 1
        if OUT.read_text() != src:
            print(f"DRIFT: {OUT} differs from freshly generated output")
            return 1
        print(f"OK: {OUT} matches")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(src)
    print(f"WROTE: {OUT} (collective-cancellation obstruction: 3 per-vertex facts + tie balance)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
