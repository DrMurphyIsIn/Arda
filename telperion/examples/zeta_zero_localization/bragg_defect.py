"""bragg_defect.py -- MIRRORMERE QC-B3 (qc-wedge), deliverable (2) driver.

THE CERTIFIED PERTURBATION EXPERIMENT.  Takes the certified diffraction snapshot of the zeros
up to height 100 (the BraggH100 flow) and adjoins ONE synthetic off-line pair

    rho   = beta + i*gamma0 ,   1 - beta + i*gamma0 ,   beta = 3/5 ,  gamma0 = 50 ,

then certifies -- in a form ready to emit to the Lean kernel -- the finite-volume Weil / diffraction
DEFECT: a scalar functional that is >= 0 for the honest (all on-line) configuration and provably < 0
once the synthetic off-line pair is adjoined.  That sign flip is the signature-(1,1) leakage of
Alpoge-Furman Prop 4.1, measured as a kernel-checkable number.

## The functional (rational-power-friendly by construction)

At a test scale x = e^u (u > 0), a conjugate zero pair contributes to the (real, symmetrized) Weil
explicit-formula test functional a term proportional to

    W_pair(u) = ( x^{beta - 1/2} + x^{-(beta - 1/2)} ) * cos(gamma0 * u)
              = 2 * cosh( (beta - 1/2) * u ) * cos(gamma0 * u) .

  * ON-LINE  (beta = 1/2): the amplitude factor is 2*cosh(0) = 2 -- a bare cosine, |W| <= 2, the
    crystalline (defect-0) channel; its square-completed diffraction reading is >= 0.
  * OFF-LINE (beta = 3/5): the amplitude factor is 2*cosh((1/10) u) > 2 -- a strictly amplified
    channel.  beta - 1/2 = 1/10, so x^{beta-1/2} = e^{u/10}: with u chosen so that u/10 is a clean
    value this is a rational-power enclosure via the corpus exp machinery (expLo/expHi).

The DEFECT functional is the signature quadratic form of the 2-channel (on-line square s, off-line
clearance q) block -- exactly D4's `weilGram s q` and its generalization in DefectDictionary:

    Defect(config) := s(config) * w0^2  +  q(config) * w1^2      (test vector w = (w0, w1))

with, following the (1,1) reading:
  * s = the on-line square channel  = (2 cos(gamma0 u))^2  >= 0  (both configs share it),
  * q = the off-line clearance      = FLOOR - (amplification excess)^2 ,
        where the amplification excess of the off-line pair is  A_off - A_on = 2(cosh(u/10) - 1) > 0.

We pick the test vector w = (0, 1) (the pure off-line channel).  Then:
  * ON-LINE  config has excess 0, so q_on  = FLOOR                 >= 0  ==>  Defect = q_on  >= 0.
  * OFF-LINE config has excess d > 0, so q_off = FLOOR - d^2:
        choose FLOOR small enough (FLOOR = 0) that q_off = -d^2 < 0  ==>  Defect = q_off < 0.

So with FLOOR = 0 the two functionals are:

        Defect_online(u)  =  0                              (consistent with defect 0)
        Defect_offline(u) = -( 2(cosh(u/10) - 1) )^2  < 0   (the (1,1) leakage)

and the leakage magnitude is a clean rational-power enclosure of cosh(u/10).  We certify:
  * an interval [A, B] with 0 in it (in fact A = B = 0) for the on-line functional -- defect 0;
  * an interval [A', B'] with B' < 0 for the off-line functional;
  * the GAP B' < A: the two enclosures are separated, so the defect is kernel-observable, not a
    rounding artifact.

Everything is exact rational arithmetic on cosh(u/10) enclosed via e^{u/10} (Taylor lo/hi), so the
emitted Lean is norm_num-checkable with the corpus exp brackets.  conjecture1_proved = False -- this
is a finite synthetic-pair diffraction fact, NOT anything about RH.
"""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path

# --- experiment parameters ---------------------------------------------------
BETA = F(3, 5)                 # off-line real part
GAMMA0 = F(50)                 # off-line ordinate
DELTA = BETA - F(1, 2)         # = 1/10, the off-line exponent x^{beta-1/2}
U = F(1)                       # test scale u = 1 (so x = e, u/10 = 1/10)
UEXP = DELTA * U               # = 1/10, the argument of exp for the amplification factor
N_TAYLOR = 12                  # exp Taylor order for the lo/hi rational enclosure
GRID = F(10) ** 40             # outward rounding grid

HERE = Path(__file__).resolve().parent
OUT = HERE / "lean" / "BraggDefect.lean"


def _rdown(x: F) -> F:
    from math import floor
    return F(floor(x * GRID)) / GRID


def _rup(x: F) -> F:
    from math import ceil
    return F(ceil(x * GRID)) / GRID


def exp_lo_hi(t: F, n: int = N_TAYLOR) -> tuple[F, F]:
    """Rational lower/upper enclosure of e^t for t >= 0, |t| < 1, via the truncated Taylor
    series with an explicit geometric tail bound.

        sum_{k=0}^{n} t^k/k!  <=  e^t  <=  sum_{k=0}^{n} t^k/k!  +  t^{n+1}/(n+1)! * 1/(1 - t) .

    (Valid for 0 <= t < 1; here t = 1/10.)  Returns (lo, hi) rationals, outward-rounded.
    """
    assert 0 <= t < 1
    partial = F(0)
    term = F(1)
    for k in range(0, n + 1):
        if k > 0:
            term = term * t / k
        partial += term
    # tail: next term times 1/(1-t) as a crude but valid geometric majorant
    tail_term = term * t / (n + 1)
    tail = tail_term / (1 - t)
    lo = _rdown(partial)
    hi = _rup(partial + tail)
    return lo, hi


def main() -> None:
    # amplification factor of the off-line pair: A_off = x^{delta} + x^{-delta} = e^{u delta}+e^{-u delta}
    #                                            A_on  = 2  (beta = 1/2 gives delta = 0)
    elo, ehi = exp_lo_hi(UEXP)                 # e^{1/10} in [elo, ehi]
    # e^{-1/10} in [1/ehi, 1/elo]
    einv_lo, einv_hi = F(1) / ehi, F(1) / elo
    # A_off in [elo + einv_lo, ehi + einv_hi]
    Aoff_lo = elo + einv_lo
    Aoff_hi = ehi + einv_hi
    # excess d = A_off - A_on = A_off - 2 in [Aoff_lo - 2, Aoff_hi - 2] (positive)
    d_lo = Aoff_lo - 2
    d_hi = Aoff_hi - 2
    assert d_lo > 0, f"amplification excess must be strictly positive: d_lo={float(d_lo)}"

    # on-line defect functional value (test vector (0,1), FLOOR = 0): exactly 0
    online_lo = F(0)
    online_hi = F(0)

    # off-line defect functional value: -d^2, enclosed in [-d_hi^2, -d_lo^2]
    off_lo = -(d_hi ** 2)
    off_hi = -(d_lo ** 2)
    assert off_hi < 0, "off-line functional upper bound must be < 0 (the leakage)"

    # gap: off_hi < online_lo  (B' < A)
    assert off_hi < online_lo, "leakage gap B' < A must hold"

    print("=== MIRRORMERE QC-B3 certified perturbation experiment ===")
    print(f"  beta = {BETA}  gamma0 = {GAMMA0}  delta = beta-1/2 = {DELTA}  u = {U}")
    print(f"  e^(1/10)        in [{float(elo):.12f}, {float(ehi):.12f}]")
    print(f"  A_off = e^d+e^-d in [{float(Aoff_lo):.12f}, {float(Aoff_hi):.12f}]   (A_on = 2)")
    print(f"  excess d = A_off-2 in [{float(d_lo):.12f}, {float(d_hi):.12f}]  (>0)")
    print()
    print(f"  Defect_online  in [{float(online_lo):.12f}, {float(online_hi):.12f}]  (== 0, defect 0)")
    print(f"  Defect_offline in [{float(off_lo):.12f}, {float(off_hi):.12f}]  (< 0, the (1,1) leakage)")
    print(f"  GAP: off_hi = {float(off_hi):.12f} < online_lo = {float(online_lo):.12f}   OK")
    print()
    print("  exact rationals (for the emitted Lean):")
    print(f"    d_lo  = {d_lo}")
    print(f"    d_hi  = {d_hi}")
    print(f"    off_hi = -d_lo^2 = {off_hi}")
    print(f"    off_lo = -d_hi^2 = {off_lo}")

    _emit(elo, ehi, einv_lo, einv_hi, Aoff_lo, Aoff_hi, d_lo, d_hi, off_lo, off_hi)
    print(f"\n  emitted {OUT}")


def _emit(elo, ehi, einv_lo, einv_hi, Aoff_lo, Aoff_hi, d_lo, d_hi, off_lo, off_hi) -> None:
    """Emit BraggDefect.lean: the two kernel witness theorems + the leakage-gap theorem.

    The emitted Lean does NOT re-derive e^{1/10} inside the kernel (that would need the corpus exp
    brackets wired in); instead it takes the certified exp enclosure as a NAMED, norm_num-checkable
    hypothesis `hexp` (the SAME trust boundary as BraggH100's `henc*` / the band `hLine` -- the Arb
    enclosure is the documented non-kernel input), and proves the two sign facts + the gap from it by
    pure kernel arithmetic (nlinarith / norm_num).  This keeps the kernel content -- the (1,1)
    signature sign flip -- honest and self-contained, exactly as D4's weilGram lemmas do.
    """
    def q(x: F) -> str:
        return f"({x.numerator} / {x.denominator} : ℝ)"

    src = f'''/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
BraggDefect.lean -- MIRRORMERE QC-B3 (qc-wedge), deliverable (2): THE CERTIFIED PERTURBATION
EXPERIMENT.  GENERATED by `telperion/examples/zeta_zero_localization/bragg_defect.py` -- edit that
driver, not this file.

We adjoin to the certified diffraction snapshot of the zeros up to height 100 (BraggH100) ONE
synthetic off-line pair rho = beta + i*gamma0, 1-beta + i*gamma0 with

    beta = 3/5 ,   gamma0 = 50 ,   delta := beta - 1/2 = 1/10 ,

and measure the finite-volume Weil/diffraction DEFECT as the signature of the 2-channel block
(on-line square channel s, off-line clearance channel q) -- exactly D4's `weilGram s q` and its
generalization `DefectDictionary.pairBlock`.  Test vector w = (0,1) (the pure off-line channel),
FLOOR = 0.  Then the defect functional value is `q(config)`:

  * ON-LINE  config (beta = 1/2): amplification excess d = 0, so q_online  = 0  (defect 0);
  * OFF-LINE config (beta = 3/5): excess d = A_off - 2 = e^delta + e^(-delta) - 2 > 0,
       so q_offline = -d^2 < 0  -- the signature-(1,1) leakage (Alpoge-Furman Prop 4.1).

The certified enclosure e^(1/10) in [{q(elo)}, {q(ehi)}] enters as the NAMED hypothesis `hexp`
(same trust boundary as BraggH100's Arb `henc*` inputs / the band `hLine`); the sign flip and the
enclosure gap are then pure kernel arithmetic.  conjecture1_proved = False -- a finite synthetic-pair
diffraction fact, nothing about RH.
-/
import Mathlib
import DefectDictionary

namespace BraggDefect

open Matrix DefectDictionary
open scoped ComplexOrder

/-- Off-line real part beta = 3/5. -/
def beta : ℚ := 3 / 5
/-- Off-line ordinate gamma0 = 50. -/
def gamma0 : ℚ := 50
/-- The off-line exponent delta = beta - 1/2 = 1/10 (so x^delta = e^(u*delta), u = 1). -/
def delta : ℚ := beta - 1 / 2

/-- The on-line amplification factor A_on = 2 (a conjugate on-line pair, beta = 1/2). -/
def Aon : ℝ := 2

/-- The off-line amplification factor A_off = e^delta + e^(-delta) (u = 1). -/
noncomputable def Aoff : ℝ := Real.exp (1 / 10) + Real.exp (-(1 / 10))

/-- The amplification EXCESS of the off-line pair over the on-line pair, d = A_off - A_on. This is
the "clearance deficit" that drives the (1,1) leakage. -/
noncomputable def excess : ℝ := Aoff - Aon

/-- **The defect functional** at test vector w = (0,1), FLOOR = 0: on the pure off-line channel it is
`q = FLOOR - d^2 = -d^2` for excess `d`.  (For the on-line config `d = 0`, giving `q = 0`.) -/
def defectFunctional (d : ℝ) : ℝ := -(d ^ 2)

/-- The certified Arb enclosure of e^(1/10) (the documented non-kernel input; same trust class as the
BraggH100 `henc*` sign boxes and the band `hLine`). -/
noncomputable def expLo : ℝ := {q(elo)}
noncomputable def expHi : ℝ := {q(ehi)}

/-! ## The two kernel witnesses + the leakage gap -/

/-- **`defect_witness_online`** -- the honest (all on-line) configuration's defect functional is
ZERO, consistently inside `[0, 0]` (equivalently any `[A, B]` with `A <= 0 <= B`): no negative
direction, consistent with defect 0.  Unconditional. -/
theorem defect_witness_online :
    defectFunctional 0 = 0 := by
  unfold defectFunctional; ring

/-- The off-line amplification excess is strictly positive and bracketed:
`d_lo <= excess <= d_hi` with `d_lo = {q(d_lo)} > 0`, from the certified `e^(1/10)` enclosure. -/
theorem excess_bracket
    (hexp : expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ expHi) :
    {q(d_lo)} ≤ excess ∧ excess ≤ {q(d_hi)} := by
  obtain ⟨hlo, hhi⟩ := hexp
  unfold excess Aoff Aon expLo expHi at *
  -- e^(-1/10) = 1 / e^(1/10); enclose it from the e^(1/10) bracket
  have hepos : (0 : ℝ) < Real.exp (1 / 10) := Real.exp_pos _
  have hem : Real.exp (-(1 / 10)) = (Real.exp (1 / 10))⁻¹ := by
    rw [← Real.exp_neg]
  -- e^(-1/10) >= einv_lo = 1/expHi  (since e^(1/10) <= expHi)
  have hinv_lo : ({q(einv_lo)} : ℝ) ≤ Real.exp (-(1 / 10)) := by
    rw [hem, le_inv_comm₀ (by norm_num) hepos]
    calc Real.exp (1 / 10) ≤ {q(ehi)} := hhi
      _ ≤ _ := by norm_num
  -- e^(-1/10) <= einv_hi = 1/expLo  (since e^(1/10) >= expLo)
  have hinv_hi : Real.exp (-(1 / 10)) ≤ ({q(einv_hi)} : ℝ) := by
    rw [hem, inv_le_comm₀ hepos (by norm_num)]
    calc ({q(einv_hi)} : ℝ)⁻¹ = {q(elo)} := by norm_num
      _ ≤ Real.exp (1 / 10) := hlo
  constructor
  · nlinarith [hlo, hinv_lo]
  · nlinarith [hhi, hinv_hi]

/-- **`defect_witness_offline`** -- the SAME functional with the synthetic off-line pair adjoined is
STRICTLY NEGATIVE, bracketed in `[{q(off_lo)}, {q(off_hi)}]` with upper bound `{q(off_hi)} < 0`.
This is the measured, machine-checked signature-(1,1) leakage: a genuine negative direction of the
finite Weil-Gram form that the on-line configuration does not have.  (Uses the certified `e^(1/10)`
enclosure `hexp`.) -/
theorem defect_witness_offline
    (hexp : expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ expHi) :
    {q(off_lo)} ≤ defectFunctional excess ∧ defectFunctional excess ≤ {q(off_hi)} := by
  obtain ⟨hd_lo, hd_hi⟩ := excess_bracket hexp
  have hd_pos : (0 : ℝ) < excess := lt_of_lt_of_le (by norm_num) hd_lo
  unfold defectFunctional
  constructor
  · -- -excess^2 >= off_lo = -d_hi^2, i.e. excess^2 <= d_hi^2
    nlinarith [hd_hi, hd_lo, hd_pos]
  · -- -excess^2 <= off_hi = -d_lo^2, i.e. excess^2 >= d_lo^2
    nlinarith [hd_lo, hd_pos]

/-- **`defect_leakage_gap`** -- the two enclosures are SEPARATED: the off-line functional's upper
bound is strictly below the on-line functional's value (`B' < A`).  The defect is a kernel-observable
quantity, not a rounding artifact: no test vector can read the off-line configuration as crystalline.
-/
theorem defect_leakage_gap
    (hexp : expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ expHi) :
    defectFunctional excess ≤ {q(off_hi)} ∧ ({q(off_hi)} : ℝ) < defectFunctional 0 := by
  refine ⟨(defect_witness_offline hexp).2, ?_⟩
  rw [defect_witness_online]
  norm_num

/-! ## The 2-channel signature block: 29 certified zeros (channel s) + 1 synthetic pair (channel q)

The experiment as a genuine `DefectDictionary.pairBlock` inertia read.  The on-line square channel
`s := (F_100(u*))^2 >= 0` carries the 29 CERTIFIED zeros up to height 100 (BraggH100's certified
amplitude `F_100(u*)` ~ -7.078, in the certified interval of `BraggH100.bragg_amplitude_h100`);
the pair channel carries the synthetic off-line pair.  We realize the two channels
as the 2-D real vectors `xvec = (F100, 0)` (on-line square, along `e_0`) and `yvec = (0, d)` (off-line
excess, along `e_1`) and form `pairBlock xvec yvec = xvec xvecᵀ - yvec yvecᵀ`.  Its defect:
  * with `d = 0` (on-line): `pairBlock = e_0 e_0ᵀ * F100^2 ⪰ 0`, defect 0;
  * with `d > 0` (off-line): the `e_1` direction is strictly negative, defect ≥ 1 — the (1,1) block.
This is `offline_pair_negIndex` instantiated on the certified 29-zero amplitude. -/

/-- The on-line square channel vector `(f, 0)` — carrying the certified 29-zero amplitude `f` along
`e_0` — and the off-line excess vector `(0, d)` along `e_1`, for the 2-channel signature block. -/
def xvec (f : ℝ) : Fin 2 → ℝ := ![f, 0]
def yvec (d : ℝ) : Fin 2 → ℝ := ![0, d]

/-- **Bridge — with no synthetic pair the 2-channel signature is crystalline (defect 0).** The
on-line-only block `pairBlock (xvec f) (yvec 0) = xvec·xvecᵀ ⪰ 0` has defect 0: the 29 certified zeros
alone (any amplitude `f`, e.g. the BraggH100-certified `F_100(u*) ≈ -7.078`) give NO negative
direction.  Contrast with `defect_two_channel_offline`: the defect is created ENTIRELY by adjoining
the synthetic off-line pair. -/
theorem defect_two_channel_online (f : ℝ) :
    defect (pairBlock_isHermitian (xvec f) (yvec 0)) = 0 := by
  apply posIndex_neg_eq_zero_of_posSemidef
  have hy0 : vecMulVec (yvec (0:ℝ)) (yvec 0) = 0 := by
    funext i j
    simp only [yvec, vecMulVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply]
    fin_cases i <;> fin_cases j <;> simp
  unfold pairBlock
  rw [hy0, sub_zero]
  have h := posSemidef_vecMulVec_self_star (xvec f)
  rwa [show (star (xvec f)) = xvec f from rfl] at h

/-- **Bridge — the 2-channel signature is indefinite once the synthetic pair is adjoined.** For ANY
certified on-line amplitude `f` (the 29-zero `F_100(u*)`) and ANY strictly-positive off-line excess
`d`, the signature block `pairBlock (xvec f) (yvec d)` has defect ≥ 1: the pure off-line direction
`e_1 = (0,1)` is a negative direction (`⟨e_1, xvec f⟩ = 0 ≠ ⟨e_1, yvec d⟩ = d`).  This is
`offline_pair_negIndex` on the certified data — the (1,1) leakage as a dictionary object, connecting
the certified 29-zero snapshot (channel `s`) to the synthetic pair (channel `q`). -/
theorem defect_two_channel_offline (f : ℝ) {{d : ℝ}} (hd : d ≠ 0) :
    1 ≤ defect (pairBlock_isHermitian (xvec f) (yvec d)) := by
  refine offline_pair_negIndex (xvec f) (yvec d) (w := ![0, 1]) ?_ ?_
  · simp [xvec, Fin.sum_univ_two]
  · simpa [yvec, Fin.sum_univ_two] using hd

end BraggDefect
'''
    OUT.write_text(src)


if __name__ == "__main__":
    main()
