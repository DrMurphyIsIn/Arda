"""Generate the complex_re_im_split dogfood: certify -> emit -> write INTO the rvm island.

    python examples/complex_re_im_split/generate.py           # write the probe file
    python examples/complex_re_im_split/generate.py --check   # drift check (no write)

Output: `examples/rvm_bridge/lean/Probes/Dogfood_complex_re_im_split.lean`, which imports the
modules it regenerates from (`E6Bridge5`, `E6Bridge7`, `E6Bridge11`, `E6Bridge14`,
`E6Bridge28`) and restates, under NEW names, the real/imaginary-part splits and cast
identities those modules prove by hand (shapes audit 48H section 2 rank 4, build order
section 7 sprint 1 item 2):

  * `E6Bridge7.lean:78-88`   (`norm_gaussTest`): the `have`s `hre` (real part of the Gaussian
    exponent) and `hsq` (`||z - c||^2`), plus the `Complex.norm_exp` step they feed;
  * `E6Bridge7.lean:105-120` (`re_gaussTest`): `hw2re`, `hw2im`, `hEre` (= `hre`), `hEim`;
  * `E6Bridge28.lean:786-807`: `re_pow_two` .. `re_pow_five` (`Re (a + b i)^N`, N = 2..5),
    each with a TIE GATE `example : <statement> := RvMBridge28.re_pow_N` so the kernel
    confirms the regenerated statement IS the hand statement;
  * the B D7 CAST FACE (`push_cast; ring` then `Complex.ofReal_re`): `E6Bridge5.lean:110-114`
    (`term_re_nonneg`), `E6Bridge7.lean:489-495` (`re_zeroSide_le`, both the cast identity
    and its `.re`), `E6Bridge11.lean:940-941` / `1336-1337` (the real product half of the
    `archSide` bookkeeping) and `E6Bridge14.lean:155-161` (`re_term_centre`), over
    natural-number / real atoms.

The E6Bridge7 split sites are local `have`s inside proofs (no exported name), so they carry
no tie gate.  Their analogue is the CONSUMER GATE footer (`CONSUMER_GATES`, hand-written and
frozen here, NOT emitter output): the two hand lemmas that consume those `have`s are (a)
pinned to themselves by a `:= RvMBridge7.<lemma>` ascription -- so the kernel confirms the
restated goal IS the hand statement -- and (b) RE-PROVED from the emitted splits alone.  The
only glue is `neg_mul` (sympy flattens `-(2 lam) * w` and `-(2 lam w)` to one Mul, so the
emitted statement can only carry the second grouping) and three `ring` reshapings (sympy's
canonical term and factor order is not the hand's); every step is `rw`/`ring`, no search
tactic.  The cast sites are local `have`s too; each carries an INSTANTIATION GATE instead:
the hand `have`'s statement, copied verbatim from the island, closed by the emitted theorem
applied to the island's atoms (`zeroMult rho`, `‖paperFT g rho.im‖`, ...), so the kernel
confirms the hand statement IS an instance of the emitted one.  The generator never runs
Lean.  The probe is the island lean_lib `DogfoodComplexReImSplit` (root
`Probes.Dogfood_complex_re_im_split`, in defaultTargets), so `lake build` compiles it and
`AxiomGuardRvMBridge.lean` prints the axioms of its fifteen theorems; to compile it alone:

    cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_complex_re_im_split.lean

conjecture1_proved = False -- finite polynomial bookkeeping; nothing here bears on RH.
"""
import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    ComplexReImSplitEmitter, ValidationReport, certify, emit,
)
from telperion.emit_complex_re_im_split import (  # noqa: E402
    IM_SYM, RE_SYM, complex_re_im_split_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_z = sp.Symbol("z")
_c, _lam = sp.symbols("c lam", real=True)
_a, _b = sp.symbols("a b", real=True)
_x, _y = RE_SYM, IM_SYM
# the Gaussian exponent of gaussTest c lam z = (z - c)^2 * exp (-(2 lam) (z - c)^2)
_EXPONENT = -(2 * _lam) * (_z - _c) ** 2
# the B D7 atoms: m a natural number (zeroMult rho), the rest real
_m = sp.Symbol("m", integer=True, nonnegative=True)
_u, _g, _v, _A, _L = sp.symbols("u g v A L", real=True)

# name -> spec, in emission order.  Claims are the hand proofs' right-hand sides.
SPECS = {
    # E6Bridge7.lean:78-88 (norm_gaussTest)
    "e6b7_hre": dict(p=_EXPONENT, mode="re", z=_z, params=(_c, _lam),
                     claim=2 * _lam * (_y ** 2 - (_x - _c) ** 2)),
    "e6b7_hsq": dict(p=_z - _c, mode="norm_sq", z=_z, params=(_c,),
                     claim=(_x - _c) ** 2 + _y ** 2),
    "e6b7_hexp": dict(p=_EXPONENT, mode="norm_exp", z=_z, params=(_c, _lam),
                      claim=2 * _lam * (_y ** 2 - (_x - _c) ** 2)),
    # E6Bridge7.lean:105-120 (re_gaussTest); hEre is hre again and is not repeated
    "e6b7_hw2re": dict(p=(_z - _c) ** 2, mode="re", z=_z, params=(_c,),
                       claim=(_x - _c) ** 2 - _y ** 2),
    "e6b7_hw2im": dict(p=(_z - _c) ** 2, mode="im", z=_z, params=(_c,),
                       claim=2 * (_x - _c) * _y),
    "e6b7_heim": dict(p=_EXPONENT, mode="im", z=_z, params=(_c, _lam),
                      claim=-(4 * _lam * (_x - _c) * _y)),
    # E6Bridge28.lean:786-807 (Re (a + b i)^N), tied to the hand lemmas
    "e6b28_re_pow_two": dict(p=(_a + _b * sp.I) ** 2, mode="re", params=(_a, _b),
                             claim=_a ** 2 - _b ** 2, tie_to="RvMBridge28.re_pow_two"),
    "e6b28_re_pow_three": dict(p=(_a + _b * sp.I) ** 3, mode="re", params=(_a, _b),
                               claim=_a ** 3 - 3 * _a * _b ** 2,
                               tie_to="RvMBridge28.re_pow_three"),
    "e6b28_re_pow_four": dict(p=(_a + _b * sp.I) ** 4, mode="re", params=(_a, _b),
                              claim=_a ** 4 - 6 * _a ** 2 * _b ** 2 + _b ** 4,
                              tie_to="RvMBridge28.re_pow_four"),
    "e6b28_re_pow_five": dict(p=(_a + _b * sp.I) ** 5, mode="re", params=(_a, _b),
                              claim=_a ** 5 - 10 * _a ** 3 * _b ** 2 + 5 * _a * _b ** 4,
                              tie_to="RvMBridge28.re_pow_five"),
    # The B D7 cast face.  E6Bridge5.lean:110-114 (term_re_nonneg, `have hcast`):
    # m := zeroMult rho, u := ‖paperFT g rho.im‖
    "e6b5_hcast": dict(p=_m * _u ** 2, mode="cast", params=(_m, _u), nat_params=(_m,),
                       claim=_m * _u ** 2),
    # E6Bridge7.lean:489-495 (re_zeroSide_le): the inner `have this` (cast identity) and the
    # outer `have hre` (its real part, by the audit's skeleton verbatim);
    # m := zeroMult rho1, g := (gaussTest c lam (gammaOf rho1)).re
    "e6b7_pair_hcast": dict(p=2 * _m * _g, mode="cast", params=(_m, _g), nat_params=(_m,),
                            claim=2 * _m * _g),
    "e6b7_pair_hre": dict(p=2 * _m * _g, mode="cast_re", params=(_m, _g), nat_params=(_m,),
                          claim=2 * _m * _g),
    # E6Bridge11.lean:940-941 and 1336-1337 (the real product half of the archSide
    # bookkeeping): A := gaussA lam, L := Real.log Real.pi.  The other half of those two
    # sites, `(1 / (2 pi)) * J`, divides by a real atom and is REFUSED (no division face).
    "e6b11_arch_hcast": dict(p=_A * _L, mode="cast", params=(_A, _L), claim=_A * _L),
    # E6Bridge14.lean:155-161 (re_term_centre): m := zeroMult rho,
    # v := -((1/2 - rho.re)^2) * Real.exp (2 lam (1/2 - rho.re)^2)
    "e6b14_centre_hcast": dict(p=_m * _v, mode="cast", params=(_m, _v), nat_params=(_m,),
                               claim=_m * _v),
}
NAMES = list(SPECS)
_ISLAND = Path(__file__).resolve().parents[1] / "rvm_bridge" / "lean"
OUT = _ISLAND / "Probes" / "Dogfood_complex_re_im_split.lean"
IMPORTS = ("E6Bridge5", "E6Bridge7", "E6Bridge11", "E6Bridge14", "E6Bridge28")

BANNER = """/-
  Dogfood_complex_re_im_split -- the Telperion `complex_re_im_split` kind
  (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 4; B N3, B D7, C 2.10, D 2.2) regenerating the
  real/imaginary-part splits and cast identities this island proves by hand, 2026-09-22:

    E6Bridge7.lean:78-88     norm_gaussTest's `hre` / `hsq` and its Complex.norm_exp step
                             (e6b7_hre, e6b7_hsq, e6b7_hexp);
    E6Bridge7.lean:105-120   re_gaussTest's `hw2re` / `hw2im` / `hEre` / `hEim`
                             (e6b7_hw2re, e6b7_hw2im, e6b7_hre, e6b7_heim);
    E6Bridge28.lean:786-807  re_pow_two .. re_pow_five, Re (a + b i)^N for N = 2..5
                             (e6b28_re_pow_*, each TIED to the hand lemma);
    E6Bridge5.lean:110-114, E6Bridge7.lean:489-495, E6Bridge11.lean:940-941 / 1336-1337,
    E6Bridge14.lean:155-161  the B D7 cast face (e6b5_hcast, e6b7_pair_hcast, e6b7_pair_hre,
                             e6b11_arch_hcast, e6b14_centre_hcast).

  The block between the telperion provenance header and the first `end DogfoodComplexReImSplit`
  is the FROZEN emitter output (examples/complex_re_im_split/generate.py regenerates it; a test
  pins the bytes).  The hand-written gates after it (1) re-prove RvMBridge7.norm_gaussTest and
  RvMBridge7.re_gaussTest from the emitted splits alone and (2) close each cast site's hand
  `have` statement, copied verbatim from the island, with the emitted theorem applied to the
  island's atoms.  Nothing in E6Bridge5 / 7 / 11 / 14 / 28 is modified.

  Built by `lake build` as the lean_lib DogfoodComplexReImSplit; AxiomGuardRvMBridge.lean prints
  the axioms of all fifteen theorems.  Alone:
    cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_complex_re_im_split.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is a finite polynomial
  identity between the components of a complex expression and real polynomials.
-/
"""


# --- the hand-written gates (frozen here; NOT emitter output) ------------------------
# The E6Bridge7 split sites are local `have`s, so they carry no tie gate.  Their analogue is
# a CONSUMER gate: re-prove the two hand lemmas that consume those `have`s -- RvMBridge7's
# norm_gaussTest and re_gaussTest -- from the emitted splits ALONE, and separately pin (by a
# `:= RvMBridge7.<lemma>` ascription) that the restated goal IS the hand lemma's statement.
# Together these say what a tie gate says for E6Bridge28: the emitter regenerates the hand
# content, and its output is strong enough to retire the hand `have`s.
#
# The glue below is the honest residue of the sympy round trip and is NOT emitted:
#   * `neg_mul`, because sympy flattens `-(2 lam) * w` and `-(2 lam w)` to the same Mul, so
#     the emitted statement can only ever carry the second grouping;
#   * two `show ... from by ring` reshapings and one final `ring`, because sympy's canonical
#     term/factor order is not the hand's (`-(x - c)^2 + y^2` vs `y^2 - (x - c)^2`,
#     `4 y lam (x - c)` vs `4 lam (x - c) y`).
# Every step is deterministic (`rw`, `ring`); no search tactic appears.
#
# The cast sites (B D7) are local `have`s too.  Each gets an INSTANTIATION gate: the hand
# `have`'s statement, copied VERBATIM from the island (a test pins the text against the
# source), proved by the emitted theorem applied to the island's atoms.  No glue at all: the
# kernel checks that the instantiated emitted statement IS the hand statement.
CONSUMER_GATES = """
/-! ## Consumer and instantiation gates (hand-written, frozen in
`examples/complex_re_im_split/generate.py`).

The E6Bridge7 split sites are local `have`s inside `RvMBridge7.norm_gaussTest` /
`RvMBridge7.re_gaussTest`, so they carry no tie gate.  Instead: each hand lemma's statement is
pinned to the hand lemma itself, and then RE-PROVED from the emitted splits above alone.  The
only glue is `neg_mul` (sympy cannot distinguish the groupings `-(2 lam) * w` and
`-(2 lam w)`) and three `ring` reshapings (sympy's canonical term order is not the hand's).
The B D7 cast sites are local `have`s too; each hand statement, copied verbatim from the
island, is closed by the emitted cast theorem applied to the island's atoms (no glue).
Nothing here is emitter output, and nothing here bears on RH.  conjecture1_proved = False. -/

namespace DogfoodComplexReImSplit

/-- Statement pin: the goal of consumer gate 1 IS `RvMBridge7.norm_gaussTest`. -/
example : ∀ (c lam : ℝ) (z : ℂ), ‖RvMBridge6.gaussTest c lam z‖ = ((z.re - c) ^ 2 + z.im ^ 2)
    * Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2)) := RvMBridge7.norm_gaussTest

/-- Consumer gate 1: `RvMBridge7.norm_gaussTest` from `e6b7_hsq` and `e6b7_hexp` alone
(the hand proof's two `have`s, `E6Bridge7.lean:78-88`). -/
example (c lam : ℝ) (z : ℂ) :
    ‖RvMBridge6.gaussTest c lam z‖ = ((z.re - c) ^ 2 + z.im ^ 2)
      * Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2)) := by
  unfold RvMBridge6.gaussTest
  rw [norm_mul, Complex.norm_pow, neg_mul, e6b7_hexp, e6b7_hsq,
    show 2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2)
        = 2 * lam * (z.im ^ 2 - (z.re - c) ^ 2) from by ring]

/-- Statement pin: the goal of consumer gate 2 IS `RvMBridge7.re_gaussTest`. -/
example : ∀ (c lam : ℝ) (z : ℂ), (RvMBridge6.gaussTest c lam z).re
    = Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2))
      * (((z.re - c) ^ 2 - z.im ^ 2) * Real.cos (4 * lam * (z.re - c) * z.im)
        + 2 * (z.re - c) * z.im * Real.sin (4 * lam * (z.re - c) * z.im)) :=
  RvMBridge7.re_gaussTest

/-- Consumer gate 2: `RvMBridge7.re_gaussTest` from `e6b7_hw2re`, `e6b7_hw2im`, `e6b7_hre` and
`e6b7_heim` alone (the hand proof's four `have`s, `E6Bridge7.lean:105-120`). -/
example (c lam : ℝ) (z : ℂ) :
    (RvMBridge6.gaussTest c lam z).re = Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2))
      * (((z.re - c) ^ 2 - z.im ^ 2) * Real.cos (4 * lam * (z.re - c) * z.im)
        + 2 * (z.re - c) * z.im * Real.sin (4 * lam * (z.re - c) * z.im)) := by
  unfold RvMBridge6.gaussTest
  rw [neg_mul, Complex.mul_re, Complex.exp_re, Complex.exp_im, e6b7_hre, e6b7_heim,
    e6b7_hw2re, e6b7_hw2im,
    show -(4 * z.im * lam * (z.re - c)) = -(4 * lam * (z.re - c) * z.im) from by ring,
    Real.cos_neg, Real.sin_neg,
    show 2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2)
        = 2 * lam * (z.im ^ 2 - (z.re - c) ^ 2) from by ring]
  ring

section CastSites
open Zeta23 WeilExplicit RvMBridge6 RvMBridge11

/-- Instantiation gate: `have hcast` of `RvMBridge5.term_re_nonneg` (`E6Bridge5.lean:110-114`)
IS `e6b5_hcast` at `m := zeroMult ρ`, `u := ‖paperFT g ρ.im‖`. -/
example (g : ℝ → ℂ) (ρ : ℂ) :
    (WeilExplicit.zeroMult ρ : ℂ) * ((‖paperFT g ρ.im‖ : ℂ)) ^ 2
        = (((WeilExplicit.zeroMult ρ : ℝ) * ‖paperFT g ρ.im‖ ^ 2 : ℝ) : ℂ) :=
  e6b5_hcast (WeilExplicit.zeroMult ρ) ‖paperFT g ρ.im‖

/-- Instantiation gate: the inner `have` of `RvMBridge7.re_zeroSide_le` (`E6Bridge7.lean:491-494`)
IS `e6b7_pair_hcast` at `m := zeroMult ρ₁`, `g := (gaussTest c lam (gammaOf ρ₁)).re`. -/
example (c lam : ℝ) (ρ₁ : ℂ) :
    (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((gaussTest c lam (gammaOf ρ₁)).re : ℂ))
        = ((2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re : ℝ) : ℂ) :=
  e6b7_pair_hcast (WeilExplicit.zeroMult ρ₁) (gaussTest c lam (gammaOf ρ₁)).re

/-- Instantiation gate: `have hre` of `RvMBridge7.re_zeroSide_le` (`E6Bridge7.lean:489-495`) IS
`e6b7_pair_hre` (whose proof is that site's `push_cast; ring` then `Complex.ofReal_re`). -/
example (c lam : ℝ) (ρ₁ : ℂ) :
    (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((gaussTest c lam (gammaOf ρ₁)).re : ℂ)).re
      = 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re :=
  e6b7_pair_hre (WeilExplicit.zeroMult ρ₁) (gaussTest c lam (gammaOf ρ₁)).re

/-- Instantiation gate: the first `show` of `RvMBridge11.re_archSide_ge` (`E6Bridge11.lean:940-941`,
repeated in `re_weilForm_gauss_nonneg_of_large_c` at `:1336-1337`) IS `e6b11_arch_hcast` at
`A := gaussA lam`, `L := Real.log Real.pi`. -/
example (lam : ℝ) :
    (gaussA lam : ℂ) * (Real.log Real.pi : ℂ) = ((gaussA lam * Real.log Real.pi : ℝ) : ℂ) :=
  e6b11_arch_hcast (gaussA lam) (Real.log Real.pi)

/-- Instantiation gate: the `have` of `RvMBridge14.re_term_centre` (`E6Bridge14.lean:155-160`) IS
`e6b14_centre_hcast` at `m := zeroMult ρ`, `v := -((1/2 - ρ.re)^2) * exp (2 lam (1/2 - ρ.re)^2)`. -/
example (lam : ℝ) (ρ : ℂ) :
    ((WeilExplicit.zeroMult ρ : ℂ)
      * ((-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2) : ℝ) : ℂ))
      = (((WeilExplicit.zeroMult ρ : ℝ)
        * (-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2)) : ℝ) : ℂ) :=
  e6b14_centre_hcast (WeilExplicit.zeroMult ρ)
    (-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2))

end CastSites

end DogfoodComplexReImSplit
"""

AXIOM_PRINTS = "\n" + "".join(
    f"#print axioms DogfoodComplexReImSplit.{nm}\n" for nm in NAMES)


def family():
    return complex_re_im_split_family(
        "DogfoodComplexReImSplit",
        GridSpec([("i", list(range(len(NAMES))))]),
        lambda pt: NAMES[pt["i"]],
        spec=lambda pt: SPECS[NAMES[pt["i"]]],
    )


def emitted_text() -> str:
    """The frozen emitter output alone (provenance header + imports + namespace + theorems)."""
    report = emit(
        certify(family()),
        LeanProfile(namespace=("DogfoodComplexReImSplit",), imports=IMPORTS),
        [ComplexReImSplitEmitter()],
        ValidationReport(checks=(("complex_re_im_split", True),)),
    )
    return next(iter(report.files.values()))


def build() -> str:
    """The complete probe: banner + frozen emitter output + hand-written gates + axiom prints."""
    return BANNER + emitted_text() + CONSUMER_GATES + AXIOM_PRINTS


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not OUT.exists() or OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: Dogfood_complex_re_im_split.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    OUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
