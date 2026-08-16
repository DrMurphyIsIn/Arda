/-
  The BUSH BOUND -- the branching-tail maximizer family, formalized.

  `general_children_crux.py` (self-verified, exhaustive over trees) shows the per-V maximiser of logPhi
  is always a DEPTH-<=2 BUSH: a root with `c` cherries and children each a bare cherry-leaf.  The near-star
  (NearStar.lean) covers only ARM children; this file covers the actual branching-tail family -- ARBITRARY
  cherry-leaf children:

      cherryLeafB c'      = node c' []                         (a c'-cherry leaf)
      cherryBushB c k c'  = node c (replicate k (cherryLeafB c'))   (root: c cherries + k c'-cherry leaves)

  RESULTS (all no-sorry):
  * `logPhi_cherryLeaf : logPhi (cherryLeafB c') = gVal c'` -- the c'-cherry leaf realises the near-star
    amplitude gVal (the leaf is a near-star of level c'); it is the GLOBAL MAXIMISER family (max gVal(5)=0),
    and `cherryLeaf_nonpos` gives <= 0 from the proven `gVal_nonpos`.
  * `cherryBush_logPhi_eq : logPhi (cherryBushB c k c') = k * gVal c' + eroot c (replicate k (cherryLeafB c'))`
    -- the exact reduction: the bush amplitude is k copies of the child amplitude gVal(c') plus the root
    increment.
  * `cherryBush_nonpos_of` : the bush is <= 0 GIVEN the per-node condition `eroot <= -(k * gVal c')` -- i.e.
    the root increment is paid by the children's negative amplitudes.  This CONDITIONAL isolates the
    branching-tail crux exactly as `Reach.phi_le_one_of_potential` isolates the general crux: the reduction
    is machine-checked; the per-node bound is the open part.
  * `cherryBush_zero : logPhi (cherryBushB c 0 c') = gVal c` -- the k=0 case is the bare c-cherry leaf,
    UNCONDITIONALLY <= 0 (it contains the tie (5,[]) = the global maximum).

  HONEST SCOPE.  The FAMILY bound (`eroot <= -(k*gVal c')` for ALL c,k,c') is the BRANCHING tail of the open
  Brualdi-Goldwasser crux -- verified numerically (77,112 bushes, max logPhi = 0 at (5,[])) and equivalent to
  the exact rational `prod Rval(c_i) * (F*fac)^11 <= (621/64)^(1+2c)` (general_children_crux.py), but NOT
  proven uniformly here.  This file formalises the reduction + the unconditional leaf/maximiser cases and
  isolates the per-node condition; it does not close the crux.  conjecture1_proved stays False.
-/
import Mathlib
import R3Cert.Reach
import R3Cert.NearStar

namespace R3Cert

open Real

/-- A bare `c'`-cherry leaf. -/
def cherryLeafB (c' : ℕ) : Branch := Branch.node c' []

/-- The depth-<=2 cherry-bush: root with `c` cherries and `k` children each a `c'`-cherry leaf. -/
def cherryBushB (c k c' : ℕ) : Branch := Branch.node c (List.replicate k (cherryLeafB c'))

/-- **`logPhi (c'-cherry leaf) = gVal c'`** -- the leaf realises the near-star amplitude of level `c'`. -/
theorem logPhi_cherryLeaf (c' : ℕ) : logPhi (cherryLeafB c') = gVal c' := by
  have hp1 : (0 : ℝ) < (3 / 2 : ℝ) ^ c' := by positivity
  have hp2 : (0 : ℝ) < 4 * (c' : ℝ) + 3 := by positivity
  have hp3 : (0 : ℝ) < rhoB ^ (1 + 2 * c') := pow_pos rhoB_pos _
  have hp4 : (0 : ℝ) < 3 * ((c' : ℝ) + 1) := by positivity
  have hac : ac c' 0 = (3 / 2 : ℝ) ^ c' * (4 * (c' : ℝ) + 3) / (rhoB ^ (1 + 2 * c') * (3 * ((c' : ℝ) + 1))) := by
    unfold ac
    push_cast
    rw [show (0 : ℝ) + 1 + (c' : ℝ) = (c' : ℝ) + 1 from by ring]
    have hc1 : (3 : ℝ) * ((c' : ℝ) + 1) ≠ 0 := by positivity
    have hr : rhoB ^ (1 + 2 * c') ≠ 0 := ne_of_gt hp3
    field_simp
    ring
  unfold cherryLeafB
  simp only [logPhi, logPhiSum, eroot, List.length_nil, cavSum, mul_zero, add_zero, zero_add,
    Real.log_one]
  rw [hac, Real.log_div (ne_of_gt (mul_pos hp1 hp2)) (ne_of_gt (mul_pos hp3 hp4)),
    Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2), Real.log_mul (ne_of_gt hp3) (ne_of_gt hp4),
    Real.log_pow, Real.log_pow, logRhoB]
  unfold gVal; push_cast; ring

/-- **`logPhi (c'-cherry leaf) <= 0`** -- from the proven `gVal_nonpos`.  The leaf family attains the global
    maximum 0 at `c' = 5` (the tie). -/
theorem cherryLeaf_nonpos (c' : ℕ) : logPhi (cherryLeafB c') ≤ 0 := by
  rw [logPhi_cherryLeaf]; exact gVal_nonpos c'

/-- **The bush reduction: `logPhi (N) = k * gVal c' + eroot`** -- k child amplitudes plus the root increment. -/
theorem cherryBush_logPhi_eq (c k c' : ℕ) :
    logPhi (cherryBushB c k c') = (k : ℝ) * gVal c' + eroot c (List.replicate k (cherryLeafB c')) := by
  unfold cherryBushB
  simp only [logPhi]
  rw [logPhiSum_replicate, logPhi_cherryLeaf]

/-- **The bush bound, CONDITIONAL on the per-node increment condition.**  If the root increment `eroot` is
    paid by the children's (negative) amplitudes -- `eroot <= -(k * gVal c')` -- then `logPhi (bush) <= 0`.
    This isolates the branching-tail crux (the condition is the open part, verified numerically). -/
theorem cherryBush_nonpos_of (c k c' : ℕ)
    (h : eroot c (List.replicate k (cherryLeafB c')) ≤ -((k : ℝ) * gVal c')) :
    logPhi (cherryBushB c k c') ≤ 0 := by
  rw [cherryBush_logPhi_eq]; linarith

/-- **`k = 0`: the bush is the bare `c`-cherry leaf, UNCONDITIONALLY `<= 0`** (contains the tie `(5,[])`). -/
theorem cherryBush_zero (c c' : ℕ) : logPhi (cherryBushB c 0 c') = gVal c := by
  simp only [cherryBushB, List.replicate_zero]
  exact logPhi_cherryLeaf c

theorem cherryBush_zero_nonpos (c c' : ℕ) : logPhi (cherryBushB c 0 c') ≤ 0 := by
  rw [cherryBush_zero]; exact gVal_nonpos c

end R3Cert
