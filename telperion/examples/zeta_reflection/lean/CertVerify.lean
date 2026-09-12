/-  CertVerify.lean -- verify-not-compute algebraic certificate checkers (A1).

    The transcendental / algebraic-irrational constants the reflection evaluators need
    (`1/√n`, `1/n`, `ln n`, `π`) are NOT computed in the kernel.  An untrusted pipeline
    supplies dyadic candidate brackets; the kernel checks a cheap ALGEBRAIC certificate that
    the candidate is a true enclosure.  This file proves each checker sound.

      * `invSqrtCert` : `l ≥ 0 ∧ l²·n ≤ 2^{2p} ≤ h²·n  →  1/√n ∈ [l·2^{-p}, h·2^{-p}]`.
      * `invCert`     : `0 < n ∧ l·n ≤ 2^p ≤ h·n        →  1/n  ∈ [l·2^{-p}, h·2^{-p}]`.
      * `lnCert`      : via exp bracketing -- `exp(l·2^{-p}) ≤ n ≤ exp(h·2^{-p})` ⇒
                        `ln n ∈ [l·2^{-p}, h·2^{-p}]` (uses `Real.exp_log`, monotone log).
      * `piCert`      : ONE dyadic π enclosure from Mathlib's `pi_gt_d20`/`pi_lt_d20`
                        (~66 bits); the plan's "try Mathlib first" branch (a Machin/arctanD
                        enclosure is only needed for >66-bit π, deferred).

    All arithmetic in the checkers is pure `Int` (`l`, `h`, `n`, `2^{2p}` compared by `Int`
    mul); the soundness lemmas bridge to ℝ.  conjecture1_proved = False.
-/
import DIntvCorrect
import TaylorKernels
import Mathlib.Analysis.Real.Pi.Bounds

open Real

namespace CertVerify

/-! ### 1/√n certificate

    Candidate: `1/√n ∈ [l·2^{-p}, h·2^{-p}]`.  Certificate (pure Int):
      `0 ≤ l  ∧  l² · n ≤ 2^{2p}  ∧  2^{2p} ≤ h² · n`.
    Soundness: squaring is monotone on nonnegatives and `√n` is the inverse of squaring, so
    `l·2^{-p} ≤ 1/√n ≤ h·2^{-p}`. -/

/-- `(2^p)² = 2^{2p}` in ℝ (zpow/nat-pow reconciliation used by the invSqrt certs). -/
private theorem two_zpow_sq (p : Nat) : ((2 : ℝ) ^ (p : Int)) ^ 2 = (2 : ℝ) ^ (2 * p) := by
  rw [← zpow_natCast ((2:ℝ)^(p:Int)) 2, ← zpow_mul, ← zpow_natCast (2:ℝ) (2*p)]
  congr 1
  push_cast
  ring

/-- Soundness of the `1/√n` certificate (lower bound). -/
theorem invSqrt_lower {n l : Int} {p : Nat} (hn : 0 < n) (hl : 0 ≤ l)
    (hcert : l ^ 2 * n ≤ (2 ^ (2 * p) : Int)) :
    (l : ℝ) * (2 : ℝ) ^ (-(p : Int)) ≤ 1 / Real.sqrt (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlR : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hsqrtpos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hppos : (0 : ℝ) < (2 : ℝ) ^ (p : Int) := DIntvProd.DIntv.two_zpow_pos _
  have hcertR : (l : ℝ) ^ 2 * (n : ℝ) ≤ ((2 : ℝ) ^ (p : Int)) ^ 2 := by
    have hc : ((l ^ 2 * n : Int) : ℝ) ≤ ((2 ^ (2 * p) : Int) : ℝ) := by exact_mod_cast hcert
    push_cast at hc
    rw [two_zpow_sq]; exact hc
  -- Reduce to `l·√n ≤ 2^p`; compare nonneg squares.
  rw [zpow_neg, ← one_div, mul_one_div, div_le_div_iff₀ hppos hsqrtpos, one_mul]
  have hlhs : (0 : ℝ) ≤ (l : ℝ) * Real.sqrt (n : ℝ) := mul_nonneg hlR (le_of_lt hsqrtpos)
  have hsq : ((l : ℝ) * Real.sqrt (n : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ (p : Int)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hnR)]; exact hcertR
  have hmain : (l : ℝ) * Real.sqrt (n : ℝ) ≤ (2 : ℝ) ^ (p : Int) :=
    (sq_le_sq₀ hlhs (le_of_lt hppos)).mp hsq
  linarith [hmain]

/-- Soundness of the `1/√n` certificate (upper bound). -/
theorem invSqrt_upper {n h : Int} {p : Nat} (hn : 0 < n) (hh : 0 ≤ h)
    (hcert : (2 ^ (2 * p) : Int) ≤ h ^ 2 * n) :
    1 / Real.sqrt (n : ℝ) ≤ (h : ℝ) * (2 : ℝ) ^ (-(p : Int)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hhR : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hsqrtpos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hppos : (0 : ℝ) < (2 : ℝ) ^ (p : Int) := DIntvProd.DIntv.two_zpow_pos _
  have hcertR : ((2 : ℝ) ^ (p : Int)) ^ 2 ≤ (h : ℝ) ^ 2 * (n : ℝ) := by
    have hc : ((2 ^ (2 * p) : Int) : ℝ) ≤ ((h ^ 2 * n : Int) : ℝ) := by exact_mod_cast hcert
    push_cast at hc
    rw [two_zpow_sq]; exact hc
  -- Reduce to `2^p ≤ h·√n`; compare nonneg squares.
  rw [zpow_neg, ← one_div, mul_one_div, div_le_div_iff₀ hsqrtpos hppos, one_mul]
  have hrhs : (0 : ℝ) ≤ (h : ℝ) * Real.sqrt (n : ℝ) := mul_nonneg hhR (le_of_lt hsqrtpos)
  have hsq : ((2 : ℝ) ^ (p : Int)) ^ 2 ≤ ((h : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hnR)]; exact hcertR
  have hmain : (2 : ℝ) ^ (p : Int) ≤ (h : ℝ) * Real.sqrt (n : ℝ) :=
    (sq_le_sq₀ (le_of_lt hppos) hrhs).mp hsq
  linarith [hmain]

/-! ### 1/n certificate -/

/-- Soundness of the `1/n` certificate (lower bound): `l·n ≤ 2^p ⇒ l·2^{-p} ≤ 1/n`. -/
theorem inv_lower {n l : Int} {p : Nat} (hn : 0 < n)
    (hcert : l * n ≤ (2 ^ p : Int)) :
    (l : ℝ) * (2 : ℝ) ^ (-(p : Int)) ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hppos : (0 : ℝ) < (2 : ℝ) ^ (p : Int) := DIntvProd.DIntv.two_zpow_pos _
  have hcertR : (l : ℝ) * (n : ℝ) ≤ (2 : ℝ) ^ (p : Int) := by
    have hc : ((l * n : Int) : ℝ) ≤ ((2 ^ p : Int) : ℝ) := by exact_mod_cast hcert
    push_cast at hc
    rw [zpow_natCast]; exact hc
  rw [zpow_neg, ← one_div, mul_one_div, div_le_div_iff₀ hppos hnR, one_mul, mul_comm]
  linarith [hcertR]

/-- Soundness of the `1/n` certificate (upper bound): `2^p ≤ h·n ⇒ 1/n ≤ h·2^{-p}`. -/
theorem inv_upper {n hh : Int} {p : Nat} (hn : 0 < n)
    (hcert : (2 ^ p : Int) ≤ hh * n) :
    1 / (n : ℝ) ≤ (hh : ℝ) * (2 : ℝ) ^ (-(p : Int)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hppos : (0 : ℝ) < (2 : ℝ) ^ (p : Int) := DIntvProd.DIntv.two_zpow_pos _
  have hcertR : (2 : ℝ) ^ (p : Int) ≤ (hh : ℝ) * (n : ℝ) := by
    have hc : ((2 ^ p : Int) : ℝ) ≤ ((hh * n : Int) : ℝ) := by exact_mod_cast hcert
    push_cast at hc
    rw [zpow_natCast]; exact hc
  rw [zpow_neg, ← one_div, mul_one_div, div_le_div_iff₀ hnR hppos, one_mul, mul_comm]
  linarith [hcertR]

/-! ### ln n certificate (via exp bracketing)

    Candidate: `ln n ∈ [lo, hi]` (reals `lo, hi`, typically `l·2^{-p}`, `h·2^{-p}`).
    Certificate: `exp lo ≤ n  ∧  n ≤ exp hi`.  Soundness: `log` is monotone and
    `log (exp lo) = lo`, so `lo = log (exp lo) ≤ log n ≤ log (exp hi) = hi`. -/

/-- Soundness of the `ln n` certificate: exp-bracket ⇒ log-bracket. -/
theorem ln_of_exp_bracket {n lo hi : ℝ} (hn : 0 < n)
    (hlo : Real.exp lo ≤ n) (hhi : n ≤ Real.exp hi) :
    lo ≤ Real.log n ∧ Real.log n ≤ hi := by
  refine ⟨?_, ?_⟩
  · have := Real.log_le_log (Real.exp_pos lo) hlo
    rwa [Real.log_exp] at this
  · have := Real.log_le_log hn hhi
    rwa [Real.log_exp] at this

/-- End-to-end `ln n` certificate wired to the Taylor exp bracket: if the untrusted pipeline
    supplies `lo, hi` with `expSeries lo N + expRem lo N ≤ n` (so `exp lo ≤ n`) and
    `n ≤ expSeries hi M − expRem hi M` (so `n ≤ exp hi`) under the reduced-arg hypotheses,
    then `ln n ∈ [lo, hi]`.  This is the composition point with `TaylorKernels`. -/
theorem ln_of_taylor_bracket {n lo hi : ℝ} {N M : ℕ}
    (hn : 0 < n) (hloAbs : |lo| ≤ 1) (hhiAbs : |hi| ≤ 1) (hN : 0 < N) (hM : 0 < M)
    (hloCert : TaylorKernels.expSeries lo N + TaylorKernels.expRem lo N ≤ n)
    (hhiCert : n ≤ TaylorKernels.expSeries hi M - TaylorKernels.expRem hi M) :
    lo ≤ Real.log n ∧ Real.log n ≤ hi := by
  have hExpLo : Real.exp lo ≤ n := le_trans (TaylorKernels.exp_upper hloAbs hN) hloCert
  have hExpHi : n ≤ Real.exp hi := le_trans hhiCert (TaylorKernels.exp_lower hhiAbs hM)
  exact ln_of_exp_bracket hn hExpLo hExpHi

/-! ### π certificate (Mathlib d20 bounds, ~66 bits) -/

/-- A rational/decimal dyadic-ready enclosure of π from Mathlib.  We expose the two Mathlib
    facts as a single bracket `[3.14159265358979323846, 3.14159265358979323847] ∋ π`.
    The A4 emitter converts these decimals to Int mantissas at a fixed exponent; the
    conversion inequality is a `norm_num` check per band, so this lemma is the trusted π seed. -/
theorem pi_bracket :
    (3.14159265358979323846 : ℝ) ≤ Real.pi ∧ Real.pi ≤ (3.14159265358979323847 : ℝ) :=
  ⟨le_of_lt Real.pi_gt_d20, le_of_lt Real.pi_lt_d20⟩

/-- π enclosed in a DIntv given a dyadic candidate `P` whose real endpoints straddle the
    Mathlib d20 decimals.  The hypotheses are the per-band `norm_num` conversion checks the
    emitter supplies (`P.lo·2^{P.e} ≤ 3.14…46` and `3.14…47 ≤ P.hi·2^{P.e}`). -/
theorem piCert {P : DIntvProd.DIntv}
    (hlo : (P.lo : ℝ) * (2:ℝ) ^ P.e ≤ (3.14159265358979323846 : ℝ))
    (hhi : (3.14159265358979323847 : ℝ) ≤ (P.hi : ℝ) * (2:ℝ) ^ P.e) :
    P.memR Real.pi := by
  obtain ⟨hpl, hph⟩ := pi_bracket
  exact ⟨le_trans hlo hpl, le_trans hph hhi⟩

end CertVerify
