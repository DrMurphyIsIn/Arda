"""Signature/statement-match gate applied to the REAL RH theorem `zeta_log_bound`.

The zero-free-region rate rests on the sharp growth bound with an EXPLICIT uniform
constant C = 6:  ‖ζ(σ+it)‖ ≤ 6·(1+log|t|).  An `∃ C` restatement compiles and is
axiom-clean but yields NO region constant — the exact bug the RH thread had to fix
by hand.  This asserts, in the Lean KERNEL, that the built `ZeroFreeBridge.zeta_log_bound`
states the intended explicit-C=6 proposition:

  * EXPLICIT C=6 (intended)   -> MATCH   (kernel confirms the exact statement)
  * EXPLICIT C=7 (weaker true bound) -> MISMATCH  (the gate pins the EXACT constant)
  * ∃C form (no region const) -> MISMATCH  (explicit vs ∃ is a different proposition)

Requires the module built:  lake build ZetaLogBound   (Mathlib olean cache present).
Run:  PATH=$HOME/.elan/bin:$PATH PYTHONPATH=src python3 scratch/rh_zeta_log_bound_signature.py
Exits non-zero unless C=6 matches and BOTH restatements are kernel-rejected.
conjecture1_proved = False.
"""
import sys
from pathlib import Path

from telperion.signature_gate import check_signatures

HERE = Path(__file__).resolve()
ENV = HERE.parents[1] / "examples" / "zero_free_bridge" / "lean"

CONTENT = "import ZetaLogBound\nopen ZeroFreeBridge\n"
_BINDERS = "{σ t : ℝ}, 1 ≤ σ → σ ≤ 2 → 2 ≤ |t| →"
_STMT = "‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≤ {C} * (1 + Real.log |t|)"

INTENDED = f"∀ {_BINDERS} " + _STMT.format(C="6")            # the claim that must hold
RESTATEMENTS = {
    "EXPLICIT C=7 (weaker true bound)": f"∀ {_BINDERS} " + _STMT.format(C="7"),
    "∃C form (no region constant)": (
        "∃ C : ℝ, ∀ {σ t : ℝ}, 1 ≤ σ → σ ≤ 2 → 2 ≤ |t| → "
        "‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≤ C * (1 + Real.log |t|)"
    ),
}


def main() -> int:
    ok = check_signatures(CONTENT, env_dir=ENV, expected={"zeta_log_bound": INTENDED})
    print(f"[intended  C=6] all_match={ok.all_match} base.okay={ok.base.okay} "
          f"axioms_clean={ok.base.axioms_clean}  (want MATCH + clean)")
    if ok.base.errors:
        print("  base errors:", ok.base.errors[:1])
    all_good = bool(ok.all_match and ok.base.axioms_clean)
    for label, restated in RESTATEMENTS.items():
        r = check_signatures(CONTENT, env_dir=ENV, expected={"zeta_log_bound": restated})
        caught = not r.all_match
        print(f"[{label:34}] all_match={r.all_match}  -> "
              f"{'MISMATCH ✗ (caught)' if caught else 'MATCH — GATE FAILED TO CATCH'}")
        all_good = all_good and caught
    print(f"\nzeta_log_bound states the intended explicit C=6 bound: {all_good}")
    print("conjecture1_proved = False.")
    return 0 if all_good else 1


if __name__ == "__main__":
    sys.exit(main())
