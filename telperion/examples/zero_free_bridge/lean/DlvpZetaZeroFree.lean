/- PHASE 4 (dVP frontier, the SELF-CONTAINED zero-free region): drop the multiplicity hypothesis.

   `dlvp_zeta_region_rate_effective` takes the zero's multiplicity `k` (with `1 ≤ k`) as input.
   `zeta_zero_divisor_pos` derives `1 ≤ divisor ζ (ball c₀ R) ρ₀` directly from `ζ ρ₀ = 0`
   (`analyticOrderAt ≥ 1` at a zero, finite because ζ is not locally zero on the connected disk —
   `ζ c₀ ≠ 0` at the centre `Re c₀ > 1`).  Feeding this in gives the fully self-contained region

     `riemannZeta_ne_zero_region` :  `55/16 ≤ |γ|` ∧ `1 - dlvpRateC/log|γ| < β`  ⟹  `ζ(β+iγ) ≠ 0`,

   i.e. `ζ(s) ≠ 0` on `Re s > 1 - dlvpRateC/log|Im s|` (for `|Im s| ≥ 55/16`), with `dlvpRateC` the
   EXPLICIT effective constant.  The `β ≥ 3/4` restriction of the rate theorem is discharged here:
   `dlvpRateC ≤ 1/1792` and `log|γ| ≥ 1`, so `1 - dlvpRateC/log|γ| > 3/4`, hence any zero in the
   region already has `β > 3/4`; and `β < 1` since ζ has no zeros with `Re ≥ 1`.

   conjecture1_proved = False (NOT a proof of RH — a kernel-verified reduction; it says a zero in the
   region cannot exist, which is what dVP gives, not a proof that ζ's zeros lie on the line).
-/
import DlvpZetaRateEffective
import DlvpZetaZeroLoc
import DlvpZetaAnaFoundation

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **`1 ≤ divisor` at a ζ-zero.**  For `ρ₀ ∈ ball c₀ R` with `ζ ρ₀ = 0`, `1 ∉ closedBall c₀ R`,
    `1 < c₀.re`: the divisor is `≥ 1` (the zero has positive, finite multiplicity). -/
theorem zeta_zero_divisor_pos {c₀ ρ₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) (hc : 1 < c₀.re)
    (hρ : ρ₀ ∈ ball c₀ R) (hzero : riemannZeta ρ₀ = 0) :
    1 ≤ divisor riemannZeta (ball c₀ R) ρ₀ := by
  have hana : AnalyticOnNhd ℂ riemannZeta (ball c₀ R) :=
    (zeta_analyticOnNhd_disk c₀ R h1).mono ball_subset_closedBall
  have hmero := hana.meromorphicOn
  have hc0mem : c₀ ∈ ball c₀ R := mem_ball_self hR
  have hconn : IsConnected (ball c₀ R) := (convex_ball c₀ R).isConnected ⟨c₀, hc0mem⟩
  have hord_c0 : meromorphicOrderAt riemannZeta c₀ ≠ ⊤ := by
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero c₀ hc0mem)]
    exact ((hana c₀ hc0mem).continuousAt.eventually_ne
      (zeta_ne_zero_of_one_lt_re c₀ hc)).filter_mono nhdsWithin_le_nhds
  have hord : meromorphicOrderAt riemannZeta ρ₀ ≠ ⊤ :=
    (hmero.exists_meromorphicOrderAt_ne_top_iff_forall hconn).1 ⟨⟨c₀, hc0mem⟩, hord_c0⟩ ⟨ρ₀, hρ⟩
  have hordne : analyticOrderAt riemannZeta ρ₀ ≠ 0 := (hana ρ₀ hρ).analyticOrderAt_ne_zero.mpr hzero
  have ha_ne_top : analyticOrderAt riemannZeta ρ₀ ≠ ⊤ := by
    intro htop
    rw [(hana ρ₀ hρ).meromorphicOrderAt_eq, htop, ENat.map_top] at hord
    exact hord rfl
  rw [hana.divisor_apply hρ]
  lift analyticOrderAt riemannZeta ρ₀ to ℕ using ha_ne_top with n
  have hn0 : n ≠ 0 := by rintro rfl; exact hordne (by simp)
  rw [ENat.map_coe, WithTop.untop₀_coe]
  omega

/-- **The self-contained de la Vallée Poussin zero-free region (EFFECTIVE constant).**
    `ζ(β+iγ) ≠ 0` whenever `|γ| ≥ 55/16` and `β > 1 - dlvpRateC/log|γ|`, with `dlvpRateC > 0` the
    explicit effective constant.  No multiplicity hypothesis. -/
theorem riemannZeta_ne_zero_region (β γ : ℝ)
    (hγ : 55/16 ≤ |γ|) (hβlow : 1 - dlvpRateC / Real.log |γ| < β) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0 := by
  intro hz
  have hβ1 : β < 1 := by
    by_contra h; push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using h) hz
  have hlogγ1 : 1 ≤ Real.log |γ| := by
    have hle : Real.exp 1 ≤ |γ| := by nlinarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log |γ| := Real.log_le_log (by positivity) hle
  have hpi : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hdK1 : 1 ≤ dlvpRateK := by
    rw [dlvpRateK]
    have hLrpos : 0 < Real.log ((23/16) / (11/8)) := Real.log_pos (by norm_num)
    have hlog15 : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hpi]; nlinarith [hpi])
    have : 0 ≤ 2 * ((8 / (3 * Real.log ((23/16) / (11/8))) + 608/9) / 16)
        * (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) := by positivity
    linarith
  have hcpos := dlvpRateC_pos
  have hcsmall : dlvpRateC ≤ 1/1792 := by
    rw [dlvpRateC, show (112:ℝ) * 16 * dlvpRateK = 1792 * dlvpRateK by ring]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hdK1])
  have hdivsmall : dlvpRateC / Real.log |γ| ≤ 1/4 := by
    have h := div_le_self (le_of_lt hcpos) hlogγ1
    linarith [h, hcsmall]
  have h34 : 3/4 ≤ β := by linarith [hβlow, hdivsmall]
  have h1c0 : (1 : ℂ) ∉ closedBall ((2 : ℂ) + (γ : ℂ) * I) (11/8) :=
    one_notMem_closedBall_of_himc (by rw [show ((2 : ℂ) + (γ : ℂ) * I).im = γ by simp]; linarith)
  have hc0re2 : (1 : ℝ) < ((2 : ℂ) + (γ : ℂ) * I).re := by
    rw [show ((2 : ℂ) + (γ : ℂ) * I).re = 2 by simp]; norm_num
  have hρmem : (β : ℂ) + (γ : ℂ) * I ∈ ball ((2 : ℂ) + (γ : ℂ) * I) (11/8) := by
    rw [mem_ball_iff_norm,
      show (β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((β - 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hk : 1 ≤ divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ((β : ℂ) + (γ : ℂ) * I) :=
    zeta_zero_divisor_pos (by norm_num) h1c0 hc0re2 hρmem hz
  have hbound := dlvp_zeta_region_rate_effective β γ
    (divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ((β : ℂ) + (γ : ℂ) * I))
    h34 hβ1 hγ hk rfl
  linarith [hbound, hβlow]

end ZeroFreeBridge

