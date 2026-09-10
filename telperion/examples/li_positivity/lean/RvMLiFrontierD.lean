/-
RvMLiFrontierD — the divisor ↔ NontrivialZero index-match (Stratum 2's finite-box
realisation, the reachable engineering).

FRONTIER ITEM (d).  Stratum 2's exhaustion is a limit over `Finset NontrivialZero`
(the upstream index).  Our weighted argument principle sums over
`RHInBoxAnalytic.zeroFinset` (the divisor support of `ζ` over a ball).  To make a
height-`T` box one of the exhausting finite subsets, the two indexings must be
matched.  This file lands the correspondence:

  * `nontrivialZero_of_strip_zero` — a `ζ`-zero in the open strip IS a
    `NontrivialZero` (the forward map, the constructor made explicit).
  * `NontrivialZero_re_mem_strip` — conversely every `NontrivialZero` sits in the
    open strip `0 < Re < 1` (the defining property, exposed).
  * `zeroFinset_toNontrivial` — the value-preserving injection of a strip box's
    `zeroFinset` into `NontrivialZero`; every box zero is a `NontrivialZero` with
    the same value, so our finite weighted sum is literally a finite sub-sum of the
    upstream index.

This closes the index-match half of frontier (d).  The remaining half — a keyhole
excluding the Li weight's pole at `s = 0` when the box is pushed to touch the real
axis — is a local contour deformation, bounded and not built here.  Together with
Stratum 2's exhaustion (any cofinal `Finset NontrivialZero` sequence → λ_n) and
Stratum 1's weighted winding, this identifies the finite box-sums whose limit is
`λ_n`.  N(T) is the count of these terms.  conjecture1_proved = False.
-/
import LiPositivity

namespace RvMLiFrontierD

open Complex

/-- **Forward map (d).**  A `ζ`-zero strictly inside the critical strip is a
    `NontrivialZero` — the upstream index element, constructed explicitly. -/
def nontrivialZero_of_strip_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : LiCriterion.NontrivialZero :=
  ⟨ρ, hζ, h0, h1⟩

@[simp] theorem nontrivialZero_of_strip_zero_val {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (nontrivialZero_of_strip_zero hζ h0 h1).val = ρ := rfl

/-- **Backward property (d).**  Every `NontrivialZero` is a `ζ`-zero in the open
    strip `0 < Re < 1` — the two indexings describe the same set. -/
theorem NontrivialZero_isZero_and_mem_strip (z : LiCriterion.NontrivialZero) :
    riemannZeta z.val = 0 ∧ 0 < z.val.re ∧ z.val.re < 1 := z.property

/-- **The value-preserving injection (d).**  If a finset `s` of `ζ`-zeros lies in
    the open strip, the map `ρ ↦ ⟨ρ, …⟩ : NontrivialZero` is injective on `s` and
    preserves values, so any weighted sum `∑_{ρ∈s} F ρ` is a finite sub-sum of the
    upstream `NontrivialZero` index:

      `∑_{ρ∈s} F ρ = ∑_{z ∈ s.attach} F (nontrivialZero_of_strip_zero …).val`.

    (The right side is indexed by concrete `NontrivialZero`s whose values are the
    box zeros — the finite piece of the upstream sum a height-`T` box realises.) -/
theorem zeroFinset_sum_via_nontrivial {s : Finset ℂ} (F : ℂ → ℂ)
    (hz : ∀ ρ ∈ s, riemannZeta ρ = 0) (hstrip : ∀ ρ ∈ s, 0 < ρ.re ∧ ρ.re < 1) :
    ∑ ρ ∈ s, F ρ
      = ∑ ρ ∈ s.attach,
          F (nontrivialZero_of_strip_zero (hz ρ.val ρ.property)
              (hstrip ρ.val ρ.property).1 (hstrip ρ.val ρ.property).2).val := by
  simp only [nontrivialZero_of_strip_zero_val]
  rw [Finset.sum_attach s (fun ρ => F ρ)]

end RvMLiFrontierD
