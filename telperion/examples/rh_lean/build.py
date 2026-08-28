"""Assemble the RH lake library from the frozen emitted Lean + transcendental
samples, so CI `lake build` actually KERNEL-CHECKS the whole RH/transcendental
line (turan/jensen/toeplitz/newton hyperbolicity + exp/log brackets).

Frozen files stay the source of truth; this copies them into RH/<Module>.lean
(module path = namespace-independent) and writes the library root.  Transcendental
certificates without an example (LogBound) get a small generated sample module.

    python3 examples/rh_lean/build.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXAMPLES = HERE.parent
sys.path.insert(0, str(EXAMPLES.parent / "src"))

from telperion import (  # noqa: E402
    GammaHalfBracketCertificate, LogBoundCertificate, PiBracketCertificate,
    SqrtBracketCertificate,
)

# frozen emitted Lean  ->  RH library module
FROZEN = {
    "Turan": "turan_xi/frozen/RiemannTuran.lean",
    "Jensen": "jensen_xi/frozen/CubicJensen.lean",
    "Toeplitz": "toeplitz_xi/frozen/ToeplitzXi.lean",
    "Newton": "newton_xi/frozen/NewtonXi.lean",
    "ExpBracket": "exp_bracket/frozen/ExpBracket.lean",
    "BGRhoBSqrt": "bg_rhob_sqrt/frozen/BGRhoBSqrt.lean",  # sqrt_bracket regenerating BG's e2 sqrt 2 crux
}


def _logbound_module() -> str:
    # a handful of in-kernel Real.log brackets (transcendental skill, no example)
    samples = [("log_two", 2, 1), ("log_three_halves", 3, 2), ("log_ten", 10, 1)]
    body = "\n\n".join(
        LogBoundCertificate(name=nm, n=n, d=d).lean().rstrip() for nm, n, d in samples)
    return ("/- Generated transcendental samples (LogBoundCertificate). -/\n"
            "import Mathlib\n\nnamespace LogBound\n\n" + body + "\n\nend LogBound\n")


def _pi_module() -> str:
    thm = PiBracketCertificate(name="pi_bracket").lean().rstrip()
    return ("/- Generated transcendental sample (PiBracketCertificate). -/\n"
            "import Mathlib\n\nnamespace PiBracket\n\n" + thm + "\n\nend PiBracket\n")


def _sqrt_module() -> str:
    samples = [("sqrt_two", 2, 1), ("sqrt_three", 3, 1), ("sqrt_ten", 10, 1)]
    body = "\n\n".join(
        SqrtBracketCertificate.build(nm, qn, qd).lean().rstrip() for nm, qn, qd in samples)
    return ("/- Generated transcendental samples (SqrtBracketCertificate). -/\n"
            "import Mathlib\n\nnamespace SqrtBracket\n\n" + body + "\n\nend SqrtBracket\n")


def _zeta_module() -> str:
    # Hand-written zeta-numerics lemmas, landed via CI iteration in the sandbox
    # (examples/mathlib_probe) and promoted here to the kernel-gated library.
    return r'''/- zeta-numerics, landed in-kernel against Mathlib v4.32.0.
   zeta(2) bounds (from pi^2/6) and zeta(3) > 9/8 (Apery's constant, NO closed
   form) via the Dirichlet series zeta_eq_tsum_one_div_nat_cpow + a partial sum. -/
import Mathlib
open scoped Real

namespace ZetaNumerics

theorem riemannZeta_two_re_bounds :
    (3 : ℝ) / 2 < (riemannZeta 2).re ∧ (riemannZeta 2).re < 8 / 3 := by
  have h : riemannZeta 2 = ((π ^ 2 / 6 : ℝ) : ℂ) := by
    rw [riemannZeta_two]; push_cast; ring
  rw [h, Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · nlinarith [Real.pi_gt_three, Real.pi_pos]
  · nlinarith [Real.pi_lt_four, Real.pi_pos]

/-- zeta(3) as a real Dirichlet series (each complex term is a nonneg real cast). -/
theorem riemannZeta_three_eq_ofReal :
    riemannZeta 3 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]
  push_cast; ring

/-- Apery's constant zeta(3) exceeds 9/8 (no closed form; first 3 series terms). -/
theorem riemannZeta_three_re_ge : (9 : ℝ) / 8 ≤ (riemannZeta 3).re := by
  rw [riemannZeta_three_eq_ofReal, Complex.ofReal_re]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h3 : (∑ n ∈ Finset.range 3, 1 / (n : ℝ) ^ 3) = 9 / 8 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  calc (9 : ℝ) / 8 = ∑ n ∈ Finset.range 3, 1 / (n : ℝ) ^ 3 := h3.symm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 3 :=
        hsum.sum_le_tsum (Finset.range 3) (fun i _ => by positivity)

end ZetaNumerics
'''


def _gammahalf_module() -> str:
    thm = GammaHalfBracketCertificate(name="gamma_half_bracket").lean().rstrip()
    return ("/- Generated: a COMPLETED in-kernel bracket of the deep transcendental\n"
            "   Gamma(1/2) = sqrt(pi) (GammaHalfBracketCertificate). -/\n"
            "import Mathlib\n\nnamespace GammaHalf\n\n" + thm + "\n\nend GammaHalf\n")


def modules() -> dict:
    out = {}
    for mod, rel in FROZEN.items():
        out[mod] = (EXAMPLES / rel).read_text()
    out["LogBound"] = _logbound_module()
    out["SqrtBracket"] = _sqrt_module()
    out["PiBracket"] = _pi_module()          # now uses confirmed Real.pi_gt_three / pi_lt_four
    out["GammaHalf"] = _gammahalf_module()   # deep transcendental Gamma(1/2), via √π + 3<π<4
    out["ZetaNumerics"] = _zeta_module()     # zeta(2) bounds + zeta(3) > 9/8 (Apery, no closed form)
    return out


def root(mods) -> str:
    return ("/- RH library root -- every module is generated/frozen. -/\n"
            + "\n".join(f"import RH.{m}" for m in mods) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    mods = modules()
    files = {f"RH/{m}.lean": text for m, text in mods.items()}
    files["RH.lean"] = root(mods)
    if args.check:
        ok = True
        for rel, text in files.items():
            p = HERE / rel
            if not p.exists() or p.read_text() != text:
                ok = False
                print(f"DRIFT: {rel}")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    (HERE / "RH").mkdir(exist_ok=True)
    for rel, text in files.items():
        (HERE / rel).write_text(text)
    print(f"assembled RH library: {len(mods)} modules ({', '.join(mods)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
