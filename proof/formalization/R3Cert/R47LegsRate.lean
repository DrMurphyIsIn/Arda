import R3Cert.R47Legs

/-!
  # The ℓ-legged growth-rate framework (stage 1: `armBase` + its key bound)

  `R47Legs.lean` proves the raw gadget pieces (the `phiL` envelope
  `phiL_le_beta`, the `483^253` bignum, the `c·ℓ ≤ 21` sweep table) but leaves
  them as orphan facts: there is no `armBase`/`rho_ell` object tying them into
  the quantified statement `rho_ℓ < rho_B for every ℓ ≠ 2`.  This file builds that
  framework, entirely in `ℚ` — the per-`(ℓ,c)` row is `armBase ℓ c ^ 11 <
  (621/64)^(1+c·ℓ)`, which is `rho_ℓ < rho_B` raised to the `11·(1+cℓ)` power, so
  no real `rpow` is ever needed (matching `legs.py`'s rational `RB = 621/64`).

  Stage 1 here is the load-bearing new content: `armBase ℓ c = phiL ℓ^c +
  c/(2(1+c))·phiL(ℓ-1)·phiL ℓ^(c-1)` (the factor by which `pi` multiplies on
  adding one ℓ-legged arm), and the structural bound

      armBase ℓ c  <  (3/2) · phiL ℓ ^ c        (ℓ ≥ 2, c ≥ 1)

  from which `armBase^11 < (3/2)^11 · phiL ℓ^(11c) ≤ (3/2)^11 · beta^(11cℓ)`
  (via `phiL_le_beta`) drives the `c·ℓ ≥ 22` tail against the bignum, and the
  `c·ℓ ≤ 21` sweep closes the finite region.  Those remaining stages build on
  `armBase_lt`.  Ground truth: `verification/legs.py` (`certify_cherries_optimal`,
  exact).  HONEST SCOPE: gadget level; the classification seam ("rate-maximal
  families have cherry arms") is named at R7' assembly.  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

/-- `phiL` is nondecreasing on `l ≥ 1` (it dips only at `0 ↦ 2, 1 ↦ 1`, then
    increases: `phiL (n+1) = phiL n + phiL (n-1)/4 ≥ phiL n`). -/
theorem phiL_mono (n : ℕ) (hn : 1 ≤ n) : phiL n ≤ phiL (n + 1) := by
  match n, hn with
  | (m + 1), _ =>
    show phiL (m + 1) ≤ phiL (m + 1) + phiL m / 4
    have := phiL_pos m
    linarith

/-- `armBase ℓ c = F_ℓ(1+c)`: the factor by which `pi` multiplies when an
    ℓ-legged arm-center (degree `1+c`) is attached, for `ℓ ≥ 2` (`delta = 2`). -/
def armBase (ell c : ℕ) : ℚ :=
  phiL ell ^ c + (c : ℚ) / (2 * (1 + c)) * phiL (ell - 1) * phiL ell ^ (c - 1)

/-- **The key structural bound**: `armBase ℓ c < (3/2)·phiL ℓ^c` for `ℓ ≥ 2`,
    `c ≥ 1`.  Reduces to the coefficient fact `c·phiL(ℓ-1) < (1+c)·phiL ℓ`
    (from `phiL(ℓ-1) ≤ phiL ℓ` and `c < 1+c`), scaled by `phiL ℓ^(c-1) > 0`. -/
theorem armBase_lt (ell c : ℕ) (hell : 2 ≤ ell) (hc : 1 ≤ c) :
    armBase ell c < 3 / 2 * phiL ell ^ c := by
  have hP : (0 : ℚ) < phiL ell := phiL_pos ell
  have hPc1 : (0 : ℚ) < phiL ell ^ (c - 1) := by positivity
  have hmono : phiL (ell - 1) ≤ phiL ell := by
    have h1 : ell - 1 + 1 = ell := by omega
    simpa [h1] using phiL_mono (ell - 1) (by omega)
  have hpc : phiL ell ^ c = phiL ell ^ (c - 1) * phiL ell := by
    rw [← pow_succ]; congr 1; omega
  have hcoef : (c : ℚ) * phiL (ell - 1) < (1 + c) * phiL ell := by
    have h2 : (c : ℚ) * phiL (ell - 1) ≤ (c : ℚ) * phiL ell :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    nlinarith [h2, hP]
  have hne : (2 * (1 + (c : ℚ))) ≠ 0 := by positivity
  simp only [armBase]
  rw [hpc, ← sub_pos]
  have hrw : 3 / 2 * (phiL ell ^ (c - 1) * phiL ell)
      - (phiL ell ^ (c - 1) * phiL ell
          + (c : ℚ) / (2 * (1 + c)) * phiL (ell - 1) * phiL ell ^ (c - 1))
      = phiL ell ^ (c - 1) * ((1 + c) * phiL ell - c * phiL (ell - 1)) / (2 * (1 + c)) := by
    field_simp
    ring
  rw [hrw]
  apply div_pos (mul_pos hPc1 (by linarith [hcoef])) (by positivity)

end Step3
end R3Cert
