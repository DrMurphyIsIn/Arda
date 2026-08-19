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

/-- The `phiL` envelope for `ℓ ≥ 3`, reindexed off `phiL_le_beta`. -/
theorem phiL_le_beta' (ell : ℕ) (h : 3 ≤ ell) : phiL ell ≤ (483 / 400 : ℚ) ^ ell := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : 3 + n = n + 3 := by omega
  rw [e]; exact phiL_le_beta n

/-- `armBase` is positive. -/
theorem armBase_pos (ell c : ℕ) : 0 < armBase ell c := by
  have hP := phiL_pos ell
  have hQ := phiL_pos (ell - 1)
  simp only [armBase]
  have h2 : 0 ≤ (c : ℚ) / (2 * (1 + c)) * phiL (ell - 1) * phiL ell ^ (c - 1) :=
    mul_nonneg (mul_nonneg (by positivity) (le_of_lt hQ)) (le_of_lt (pow_pos hP _))
  have h1 : 0 < phiL ell ^ c := pow_pos hP c
  linarith

/-- **Stage 2 — the envelope combination**: `armBase ℓ c ^ 11 < (3/2)^11 ·
    beta^(11·c·ℓ)` for `ℓ ≥ 3`.  Chains `armBase_lt` (raised to the 11th power)
    with `phiL_le_beta'`.  This is the object the `c·ℓ ≥ 22` tail bounds against
    the `483^253` bignum. -/
theorem armBase_pow11_le (ell c : ℕ) (hell : 3 ≤ ell) (hc : 1 ≤ c) :
    armBase ell c ^ 11 < (3 / 2 : ℚ) ^ 11 * (483 / 400 : ℚ) ^ (11 * c * ell) := by
  have h1 : armBase ell c < 3 / 2 * phiL ell ^ c := armBase_lt ell c (by omega) hc
  have h0 : (0 : ℚ) ≤ armBase ell c := le_of_lt (armBase_pos ell c)
  have hPnn : (0 : ℚ) ≤ phiL ell := le_of_lt (phiL_pos ell)
  have hbeta : phiL ell ≤ (483 / 400 : ℚ) ^ ell := phiL_le_beta' ell hell
  have hexp : (483 / 400 : ℚ) ^ (11 * c * ell) = ((483 / 400 : ℚ) ^ ell) ^ (11 * c) := by
    rw [← pow_mul]; congr 1; ring
  have hphi : phiL ell ^ (11 * c) ≤ ((483 / 400 : ℚ) ^ ell) ^ (11 * c) :=
    pow_le_pow_left₀ hPnn hbeta (11 * c)
  calc armBase ell c ^ 11
      < (3 / 2 * phiL ell ^ c) ^ 11 := pow_lt_pow_left₀ h1 h0 (by norm_num)
    _ = (3 / 2 : ℚ) ^ 11 * phiL ell ^ (11 * c) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm c 11]
    _ ≤ (3 / 2 : ℚ) ^ 11 * ((483 / 400 : ℚ) ^ ell) ^ (11 * c) :=
        mul_le_mul_of_nonneg_left hphi (by positivity)
    _ = (3 / 2 : ℚ) ^ 11 * (483 / 400 : ℚ) ^ (11 * c * ell) := by rw [hexp]

/-- `beta^11 < rho_B^11`: the per-step ratio driving the tail. -/
theorem beta11_lt : (483 / 400 : ℚ) ^ 11 < 621 / 64 := by norm_num

/-- The tail base case `k = 22` (a `norm_num` bignum, `483^242`-class). -/
theorem tail_base :
    (3 / 2 : ℚ) ^ 11 * (483 / 400) ^ (11 * 22) < (621 / 64) ^ 23 := by norm_num

/-- **Stage 3 — the `c·ℓ ≥ 22` tail**, as a rational induction on `k = c·ℓ`:
    `(3/2)^11 · beta^(11k) < (621/64)^(1+k)` for `k ≥ 22`.  Base `k=22` is the
    bignum; the step multiplies by `beta^11 < 621/64`. -/
theorem tail_rat (k : ℕ) (hk : 22 ≤ k) :
    (3 / 2 : ℚ) ^ 11 * (483 / 400) ^ (11 * k) < (621 / 64) ^ (1 + k) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using tail_base
  | succ k hk ih =>
    have hRpos : (0 : ℚ) < (621 / 64) ^ (1 + k) := by positivity
    have eL : (3 / 2 : ℚ) ^ 11 * (483 / 400) ^ (11 * (k + 1))
        = ((3 / 2 : ℚ) ^ 11 * (483 / 400) ^ (11 * k)) * (483 / 400) ^ 11 := by
      rw [Nat.mul_succ, pow_add]; ring
    have eR : (621 / 64 : ℚ) ^ (1 + (k + 1)) = (621 / 64) ^ (1 + k) * (621 / 64) := by
      rw [show 1 + (k + 1) = (1 + k) + 1 by omega, pow_succ]
    rw [eL, eR]
    calc ((3 / 2 : ℚ) ^ 11 * (483 / 400) ^ (11 * k)) * (483 / 400) ^ 11
        < (621 / 64) ^ (1 + k) * (483 / 400) ^ 11 :=
          mul_lt_mul_of_pos_right ih (by positivity)
      _ ≤ (621 / 64) ^ (1 + k) * (621 / 64) :=
          mul_le_mul_of_nonneg_left (le_of_lt beta11_lt) (le_of_lt hRpos)

/-- **Stage 3 assembly**: the ℓ≥3 rate row in the tail region `c·ℓ ≥ 22`:
    `armBase ℓ c ^ 11 < (621/64)^(1+c·ℓ)`. -/
theorem armBase_rate_tail (ell c : ℕ) (hell : 3 ≤ ell) (hc : 1 ≤ c)
    (hk : 22 ≤ c * ell) :
    armBase ell c ^ 11 < (621 / 64 : ℚ) ^ (1 + c * ell) := by
  calc armBase ell c ^ 11
      < (3 / 2 : ℚ) ^ 11 * (483 / 400 : ℚ) ^ (11 * c * ell) :=
        armBase_pow11_le ell c hell hc
    _ = (3 / 2 : ℚ) ^ 11 * (483 / 400 : ℚ) ^ (11 * (c * ell)) := by rw [Nat.mul_assoc]
    _ < (621 / 64) ^ (1 + c * ell) := tail_rat (c * ell) hk

/-- **Stage 4 — the assembled ℓ≥3 rate rows**: `armBase ℓ c ^ 11 <
    (621/64)^(1+c·ℓ)` for EVERY `ℓ ≥ 3` and `c ≥ 1` — i.e. `rho_ℓ < rho_B`, so a
    star whose legs have length `ℓ ≥ 3` grows strictly slower than the cherry
    star.  The `c·ℓ ≥ 22` tail is `armBase_rate_tail`; the `c·ℓ ≤ 21` finite
    region is closed by evaluating `armBase` (through `phiL`) per cell.  Gadget
    level; the classification seam ("rate-maximal families have cherry arms") is
    named at R7' assembly.  conjecture1_proved = False. -/
theorem legs_rate_ge3 (ell c : ℕ) (hell : 3 ≤ ell) (hc : 1 ≤ c) :
    armBase ell c ^ 11 < (621 / 64 : ℚ) ^ (1 + c * ell) := by
  rcases Nat.lt_or_ge (c * ell) 22 with h | h
  · have hce : c * ell ≤ 21 := by omega
    have hue : ell ≤ 21 := le_trans (Nat.le_mul_of_pos_left ell (by omega)) hce
    have huc : c ≤ 21 := le_trans (Nat.le_mul_of_pos_right c (by omega)) hce
    interval_cases ell <;> interval_cases c <;>
      first | omega | norm_num [armBase, phiL]
  · exact armBase_rate_tail ell c hell hc h

end Step3
end R3Cert
