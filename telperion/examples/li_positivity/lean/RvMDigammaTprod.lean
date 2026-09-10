/-
RvMDigammaTprod — Phase 2 brick 4 (part 3): the log-derivative of the Weierstrass product.

Assembles the per-factor log-derivative (`logDeriv_wFactor`) and its summability
(`summable_logDeriv_wFactor`) through Mathlib's `logDeriv_tprod_eq_tsum`, using the product's
local-uniform convergence (b2) and its non-vanishing (from b3's `weierstrass_prod_eq_inv_Gamma`):

  * `logDeriv_tprod_wFactor` — `logDeriv (∏'_n wFactor n ·) s = ∑'_n (1/(s+(n+1)) − 1/(n+1))`.

This IS the digamma series, phrased via the log-derivative of the Weierstrass product.  The final
identification with the named `Complex.digamma` (via `s·e^{γs}·∏' = 1/Γ` on a pole-free
neighbourhood) is the remaining b4 step.  conjecture1_proved = False.
-/
import Mathlib
import RvMDigammaSummable
import RvMDigammaProd

open Complex

namespace RvMWeierstrass

set_option maxHeartbeats 1000000 in
/-- **Log-derivative of the Weierstrass product = the digamma series.**  For `s` off the poles,
    `logDeriv (∏'_n wFactor n ·) s = ∑'_n (1/(s+(n+1)) − 1/(n+1))`.  Via `logDeriv_tprod_eq_tsum`
    (open `univ`; factors entire and non-zero at `s`; summands summable; product locally-uniformly
    convergent from b2; product non-zero at `s` from b3). -/
theorem logDeriv_tprod_wFactor {s : ℂ} (hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0) :
    logDeriv (fun z : ℂ => ∏' n : ℕ, wFactor n z) s
      = ∑' n : ℕ, (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)) := by
  -- each factor is non-zero at s (off its pole −(n+1))
  have hf : ∀ n : ℕ, wFactor n s ≠ 0 := by
    intro n
    refine wFactor_ne_zero ?_
    intro hc; exact hs (n + 1) (by push_cast; rw [hc]; ring)
  -- each factor is entire
  have hd : ∀ n : ℕ, DifferentiableOn ℂ (wFactor n) Set.univ := by
    intro n
    have : Differentiable ℂ (wFactor n) := by
      unfold wFactor; fun_prop
    exact this.differentiableOn
  have hm : Summable (fun n => logDeriv (wFactor n) s) := summable_logDeriv_wFactor hs
  have htend : MultipliableLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => wFactor n z)
      (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_wFactor.multipliableLocallyUniformlyOn
  -- the product is non-zero at s, from b3 (Γ⁻¹ ≠ 0)
  have hnez : ∏' n : ℕ, wFactor n s ≠ 0 := by
    intro hzero
    have hb3 := weierstrass_prod_eq_inv_Gamma hs
    rw [hzero, mul_zero] at hb3
    have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (fun m h => hs m (by rw [h]; ring))
    exact (inv_ne_zero hΓ) hb3.symm
  rw [logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ s) hf hd hm htend hnez]
  refine tsum_congr (fun n => ?_)
  have h : s + ((n : ℂ) + 1) ≠ 0 := by have := hs (n + 1); push_cast at this; exact this
  exact logDeriv_wFactor h

end RvMWeierstrass
