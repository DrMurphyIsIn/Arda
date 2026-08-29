"""23-gate-strictness arithmetic anchor, kernel-gated.

PROOF_STATUS's live lead: the BG deficit `1 - Phi^11 = M/D` (M = 621^n Q^11 - 64^n P^11,
prod a_v = P/Q) is bounded below by an ARITHMETIC quantity `23^{v_23(M)}/D`, refining the
crude integrality floor `1/D`.  The module `gate_strictness.py` establishes this in exact
Fraction arithmetic, but its own `.lean()` was a stub (`(64:ℤ) * ? = 621`) -- never
kernel-checked.  This regenerates the anchor as VALID, kernel-checkable Lean.

Emitted for the tie-recursive family `hub + k*N(0,5)` (n = 11k+1), where the 23-gate is
STRONGEST (the two terms are 23-adically close, `v_23(M) = 11(k-1)` growing linearly):
  * `deficit_pos_k{k}` : `0 < M_k`  -- the deficit numerator is a positive integer (strict:
    non-tie => Phi^11 < 1, given the open `<=` half);
  * `deficit_v23_k{k}` : `23^{11(k-1)} | M_k  &&  not 23^{11(k-1)+1} | M_k` -- the EXACT
    23-adic valuation, so `1 - Phi^11 >= 23^{11(k-1)}/D` (the quantitative refinement).

The linear growth `v_23(M_k) = 0, 11, 22, ...` is thus kernel-verified on the family that
approaches Phi^11 = 1.  HONEST SCOPE: this quantifies STRICTNESS (the `<` with an arithmetic
factor); it does NOT prove the `<=` half (the open collective-cancellation crux).  The
anchor constant `v_23(621) = 1` (23 || 621 = 3^3*23) is gated separately in padic_valuation.
conjecture1_proved = False.

    python3 examples/bg_gate_strictness/generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.gate_strictness import deficit_23_valuation, deficit_integer  # noqa: E402
from telperion.frustration_free import tie_recursive_edges  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE / "frozen" / "BGGateStrictness.lean"
KS = (1, 2, 3)  # tie-recursive levels: n = 11k+1 = 12, 23, 34 (M up to ~162 digits)


def _facts():
    out = []
    for k in KS:
        n, e = tie_recursive_edges(k)
        M, _D = deficit_integer(n, e, 0)
        v = deficit_23_valuation(n, e, 0)
        assert M > 0 and v == 11 * (k - 1), (k, M, v)
        out.append((k, n, M, v, 23 ** v, 23 ** (v + 1)))
    return out


def build() -> str:
    lines = []
    for k, n, M, v, lo_div, hi_div in _facts():
        lines.append(
            f"-- tie-recursive k={k} (n={n}): deficit M has {len(str(M))} digits, v_23(M)={v}=11*(k-1)\n"
            f"theorem deficit_pos_k{k} : (0 : ℤ) < {M} := by norm_num\n\n"
            f"theorem deficit_v23_k{k} :\n"
            f"    (({lo_div} : ℤ) ∣ {M}) ∧ ¬ (({hi_div} : ℤ) ∣ {M}) := by norm_num"
        )
    body = "\n\n".join(lines)
    header = (
        "/- 23-gate-strictness arithmetic anchor (PROOF_STATUS live lead), kernel-gated.\n"
        "   Deficit M_k = 621^n Q^11 - 64^n P^11 for the tie-recursive family hub + k*N(0,5)\n"
        "   (n = 11k+1): M_k > 0 (strict, non-tie) and v_23(M_k) = 11(k-1) EXACTLY, so\n"
        "   1 - Phi^11 >= 23^{11(k-1)}/D -- the arithmetic refinement, strongest on the near-1\n"
        "   family.  Quantifies strictness; does NOT prove the open <= half.  Via Int divisibility. -/\n"
        "import Mathlib\n\nnamespace BGGateStrictness\n\n"
    )
    return header + body + "\n\nend BGGateStrictness\n"


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
    print(f"WROTE: {OUT} ({len(KS)} tie-recursive deficit certificates)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
