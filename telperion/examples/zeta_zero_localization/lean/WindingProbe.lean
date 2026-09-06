import Mathlib

/-!
# Stage-2 feasibility probe: WindingProbe

PROBE ARTIFACT — not wired into any CI build target.  It is NOT declared in
`lakefile.toml` (`defaultTargets = ["LambdaLineReal", "XiLineZeros"]`) and is
imported by neither default target, so the example's `lake build` never
compiles it; it is an inert file kept alongside the findings doc.

Purpose: confirm that the composition `(2πi)⁻¹ ∮ f = Σ m` closes over the SAME
Mathlib lemma chain that `full_argument_principle` (kernel-verified on
origin/main, PR #262) is built from, by exercising it on a toy
`f z = 2 * (z - c0)⁻¹ + 0` (single pole of multiplicity 2 at `c0`, analytic
remainder `E = 0`), obtaining `∮_{C(c0, 3/2)} f = 4πi`.

SCOPE HONESTY: this file does NOT import `FullArgumentPrinciple` and invoke
`full_arg_principle_3half` as a black box — that would couple this example
target to the `dvp_geom_atoms` example.  Instead it re-derives the result from
the identical base lemmas (`circleIntegral.integral_sub_inv_of_mem_ball` +
`integral_const_mul`) that PR #262's artifact uses.  So it demonstrates that
the underlying Mathlib chain composes as claimed, NOT that the atom's exact
interface has been matched here — the interface match is the ~1-day hypothesis-
matching step estimated in ZEROLOC_STAGE2_PROBE.md, not this probe.  The
theorem below is sorry-free.

Assembly path being probed:
  full_argument_principle (∮ Σ m/(z-ρ) + E = 2πi·Σ m, E holomorphic, generic center c)
    ← applied with f = Σ m/(z-ρ) + 0, s = {c0}, m = const 2, E = 0
  ↓
  ∮_{C(c0, 3/2)} f = 2πi · 2 = 4πi        [this file, sorry-free]

Gap confirmed: the Blaschke split logDeriv_eq_herglotz_add_entire lives at center 0
(ball 0 R).  The glue lemma needed for Stage 2 proper is a center-0-to-c SHIFT that
re-expresses logDeriv ζ z = Σ (divisor ρ)/(z-ρ) + E for ρ ∈ ball c R (not ball 0 R).

conjecture1_proved = False (NOT a proof of RH).
-/

open Complex Metric Real

namespace WindingProbe

/-- Toy composition: for `f z = 2 * (z - c0)⁻¹` (a single pole of multiplicity 2 at `c0`
    inside the disk of radius 3/2), `∮_{C(c0, 3/2)} f = 4πi`.

    Proof: instantiate `full_argument_principle` with `s = {c0}`, `m = fun _ => 2`,
    `E = fun _ => 0` (trivially holomorphic), `f z = 2*(z-c0)⁻¹ + 0 = 2*(z-c0)⁻¹`.
    The kernel lemma `circleIntegral.integral_sub_inv_of_mem_ball` + linearity closes it.

    This is sorry-free: every step uses kernel-verified Mathlib lemmas identical to
    those used by PR #262's FullArgumentPrinciple artifact. -/
theorem winding_probe_single_pole (c0 : ℂ) :
    (∮ z in C(c0, (3 / 2 : ℝ)), 2 * (z - c0)⁻¹) = 4 * π * I := by
  have hR : (0 : ℝ) < 3 / 2 := by norm_num
  -- c0 is in ball c0 (3/2) since dist c0 c0 = 0 < 3/2
  have hmem : c0 ∈ ball c0 ((3 / 2) : ℝ) := by
    simp [mem_ball, dist_self, hR]
  -- (z - c0)⁻¹ is circle-integrable on C(c0, 3/2)
  have hbase : CircleIntegrable (fun z => (z - c0)⁻¹) c0 ((3 / 2) : ℝ) := by
    rw [circleIntegrable_sub_inv_iff]
    exact Or.inr (by rw [mem_sphere, dist_self, abs_of_pos hR]; norm_num)
  -- Linearity: ∮ 2*(z-c0)⁻¹ = 2 * ∮ (z-c0)⁻¹
  rw [show (fun z => 2 * (z - c0)⁻¹) = (fun z => (2 : ℂ) * (z - c0)⁻¹) from rfl,
    circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball hmem]
  ring

/-- The same result phrased as a zero-count: `(2πi)⁻¹ · ∮_{C(c0,3/2)} f = 2`.
    Confirms that the contour integral recovers the multiplicity (2) at c0. -/
theorem winding_probe_count (c0 : ℂ) :
    (2 * π * I)⁻¹ * (∮ z in C(c0, (3 / 2 : ℝ)), 2 * (z - c0)⁻¹) = 2 := by
  rw [winding_probe_single_pole]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  field_simp
  ring

end WindingProbe
