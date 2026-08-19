import R3Cert.R47Legs
import R3Cert.R47LegsRate

/-!
  # R2 rung assembly: legs are cherries (2026-08-19)

  The R2 rung of the Brualdi–Goldwasser reduction (`conjecture1_status.py`): a star
  whose legs are not cherries (length ≠ 2) grows strictly slower than `rho_B`, so
  `Φ`-maximizers have cherry legs.  Both hard cases are already kernel-checked:

  - **ℓ = 1** — `ell1_rate` (`R47Legs.lean`): `((1+2c)/(1+c))^11 < (621/64)^(1+c)`.
  - **ℓ ≥ 3** — `legs_rate_ge3` (`R47LegsRate.lean`): `armBase ℓ c ^11 < (621/64)^(1+cℓ)`,
    via the F_ℓ growth-rate framework.

  This file **assembles** them into the single rung statement `legs_are_cherries`,
  quantified over every leg length `ℓ ≥ 1, ℓ ≠ 2` and every `c ≥ 1` (ℓ = 2 is the
  cherry, the optimum, not a "beats" case).  The bridge is `armBase 1 c = (1+2c)/(1+c)`
  (`phiL 0 = 2`, `phiL 1 = 1`), so the ℕ `ell1_rate` is exactly the ℓ = 1 instance of
  the ℚ `armBase` form.  Gadget-level (growth-rate) content; the classification seam is
  named at R7' assembly.  Ground truth: `verification/legs.py`.  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

/-- `armBase 1 c = (1 + 2c)/(1 + c) = F_1(1+c)` — the single-leg amplitude, from
    `phiL 1 = 1`, `phiL 0 = 2`. -/
theorem armBase_one (c : ℕ) : armBase 1 c = (1 + 2 * (c : ℚ)) / (1 + (c : ℚ)) := by
  have h0 : phiL 0 = 2 := rfl
  have h1 : phiL 1 = 1 := rfl
  have hden : (1 + (c : ℚ)) ≠ 0 := by positivity
  simp only [armBase, Nat.sub_self, h0, h1, one_pow, mul_one]
  field_simp
  ring

/-- The ℓ = 1 rate row in the `armBase`/ℚ form (bridged from the ℕ `ell1_rate`). -/
theorem armBase_one_rate (c : ℕ) (hc : 1 ≤ c) :
    armBase 1 c ^ 11 < (621 / 64 : ℚ) ^ (1 + c) := by
  rw [armBase_one, div_pow, div_pow,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  push_cast
  exact_mod_cast ell1_rate c hc

/-- **R2 (legs are cherries).** Every leg of length `ℓ ≥ 1`, `ℓ ≠ 2`, is
    rate-suboptimal: its arm factor is strictly below the cherry rate `rho_B`,
    `armBase ℓ c ^ 11 < (621/64)^(1 + cℓ)` for every `c ≥ 1`.  Combines the ℓ = 1
    and ℓ ≥ 3 leaves; ℓ = 2 is the cherry (the optimum). -/
theorem legs_are_cherries (ell c : ℕ) (hell : 1 ≤ ell) (hne : ell ≠ 2) (hc : 1 ≤ c) :
    armBase ell c ^ 11 < (621 / 64 : ℚ) ^ (1 + c * ell) := by
  rcases Nat.lt_or_ge ell 3 with h | h
  · interval_cases ell
    · simpa using armBase_one_rate c hc
    · exact absurd rfl hne
  · exact legs_rate_ge3 ell c h hc

end Step3
end R3Cert
