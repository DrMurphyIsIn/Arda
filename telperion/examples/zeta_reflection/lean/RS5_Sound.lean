/-  RS5_Sound.lean -- lane B5: SOUNDNESS of the t >= 509 checker `RS5.check5`.

    This file is lane B4's `RS4_Sound` sections 1-9 (the checker's facts over the reals, the DIntv
    assembly and the soundness theorem) re-stated for `RS5.Checks5`, which differs from `RS4.Checks`
    ONLY in the height floor (`509 * 2^tq <= tn` instead of `10000 * 2^tq <= tn`).  The floor is used by
    exactly two facts, `t_ge` and `tn_pos`; every other proof is unchanged text.  The height-free
    helpers of `RS4_Sound` (`Zmain`, `Lser`, `log_one_add_near`, `lp_real`, `ballD_mem`, ...) and all
    computable definitions of `RS4_Eval` are REUSED (selective `open RS4 (...)`), not duplicated.

    ## The headline

      `RS5.check5_sound` : `Valid c t K` and `check5 c z = true` imply
        `509 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and for EVERY phase
        `phi` with `|phi - rsThetaMain t| <= 1/t`:  `zlo / 2^(2P) <= RS4.Zmain t phi <= zhi / 2^(2P)`.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/
import RS5_Eval
import RS4_Sound

open Real Finset
open ArbEcon DIntvProd
open RS4 (Cert lpPos lpNeg sgnI ballD negIf dstate phTrig mainBox c0Box zBox QuotOK Zmain Lser
  log_one_add_near lp_real sgnI_cast two_zpow_negP ballD_mem brD_mem negIf_mem)

namespace RS5

noncomputable section

/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}

theorem oneR (hv : Valid c t K) : (c.one : ℝ) = 2 ^ c.P := by
  rw [hv.one_eq]; push_cast; ring

theorem pi_lo (hv : Valid c t K) : (c.hp : ℝ) - c.rp ≤ π / 2 * 2 ^ c.P := by
  have := hv.pi_ball; rw [abs_le] at this; linarith [this.1]

theorem pi_hi (hv : Valid c t K) : π / 2 * 2 ^ c.P ≤ (c.hp : ℝ) + c.rp := by
  have := hv.pi_ball; rw [abs_le] at this; linarith [this.2]

theorem t_ge (hv : Valid c t K) (hk : Checks5 c z) : 509 ≤ t := by
  rw [hv.t_eq, le_div_iff₀ (by positivity)]
  have := hk.ht
  exact_mod_cast this

theorem t_pos (hv : Valid c t K) (hk : Checks5 c z) : 0 < t := by
  linarith [t_ge hv hk]

/-- `a = rsAlpha t` squared. -/
theorem alpha_sq (ht : 0 < t) : RSInt.rsAlpha t ^ 2 = t / (2 * π) :=
  Real.sq_sqrt (by positivity)

theorem alpha_nonneg (t : ℝ) : 0 ≤ RSInt.rsAlpha t := Real.sqrt_nonneg _

/-- `(a 2^P)^2 * (2^tq * 4 * (pi/2 * 2^P)) = tn * 2^(3P)`. -/
theorem alpha_key (hv : Valid c t K) (hk : Checks5 c z) :
    (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) =
      (c.tn : ℝ) * (2 ^ c.P * 2 ^ c.P * 2 ^ c.P) := by
  have ht := t_pos hv hk
  have hq : (0 : ℝ) < 2 ^ c.tq := by positivity
  rw [mul_pow, alpha_sq ht, hv.t_eq]
  field_simp
  ring

theorem A0_le (hv : Valid c t K) (hk : Checks5 c z) :
    (z.A0 : ℝ) ≤ RSInt.rsAlpha t * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hq : (0 : ℝ) < 2 ^ c.tq := by positivity
  have h := hk.hA0
  have hR : ((z.A0 * z.A0 * 2 ^ c.tq * 4 * (c.hp + c.rp) : ℕ) : ℝ)
      ≤ ((c.tn * (c.one * c.one * c.one) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  rw [oneR hv] at hR
  have key := alpha_key hv hk
  have hpi := pi_hi hv
  have hx := mul_nonneg (alpha_nonneg t) hP.le
  by_contra hcon
  rw [not_le] at hcon
  have hsq : (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 < (z.A0 : ℝ) ^ 2 := by
    apply pow_lt_pow_left₀ hcon hx (by norm_num)
  have hw : (0 : ℝ) < 2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P) := by positivity
  have h1 : (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      < (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) := mul_lt_mul_of_pos_right hsq hw
  have h2 : (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      ≤ (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * ((c.hp : ℝ) + c.rp)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left hpi (by positivity)
  nlinarith

theorem A1_ge (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsAlpha t * 2 ^ c.P ≤ (z.A1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h := hk.hA1
  have hR : ((c.tn * (c.one * c.one * c.one) : ℕ) : ℝ)
      ≤ ((z.A1 * z.A1 * 2 ^ c.tq * 4 * (c.hp - c.rp) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub hk.hrp] at hR
  rw [oneR hv] at hR
  have key := alpha_key hv hk
  have hpi := pi_lo hv
  have hx := mul_nonneg (alpha_nonneg t) hP.le
  by_contra hcon
  rw [not_le] at hcon
  have hsq : (z.A1 : ℝ) ^ 2 < (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 := by
    apply pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  have hpipos : (0 : ℝ) < π / 2 * 2 ^ c.P := by positivity
  have h2 : (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * ((c.hp : ℝ) - c.rp))
      ≤ (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left hpi (by positivity)
  have hw : (0 : ℝ) < 2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P) := by positivity
  have h1 : (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      < (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) :=
    mul_lt_mul_of_pos_right hsq hw
  nlinarith

theorem N_lt_alpha (hv : Valid c t K) (hk : Checks5 c z) : (z.N : ℝ) < RSInt.rsAlpha t := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((z.N * c.one : ℕ) : ℝ) < (z.A0 : ℝ) := by exact_mod_cast hk.hNlo
  push_cast at h; rw [oneR hv] at h
  have := A0_le hv hk
  by_contra hc; rw [not_lt] at hc
  nlinarith

theorem alpha_lt_N1 (hv : Valid c t K) (hk : Checks5 c z) : RSInt.rsAlpha t < (z.N : ℝ) + 1 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : (z.A1 : ℝ) < (((z.N + 1) * c.one : ℕ) : ℝ) := by exact_mod_cast hk.hNhi
  push_cast at h; rw [oneR hv] at h
  have := A1_ge hv hk
  by_contra hc; rw [not_lt] at hc
  nlinarith

theorem N_eq (hv : Valid c t K) (hk : Checks5 c z) : RSInt.rsNn t = z.N := by
  unfold RSInt.rsNn
  rw [Nat.floor_eq_iff (alpha_nonneg t)]
  exact ⟨(N_lt_alpha hv hk).le, alpha_lt_N1 hv hk⟩

theorem frac_eq (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t = RSInt.rsAlpha t - z.N := by
  unfold RSInt.rsFrac; rw [N_eq hv hk]

theorem frac_pos (hv : Valid c t K) (hk : Checks5 c z) : 0 < RSInt.rsFrac t := by
  rw [frac_eq hv hk]; linarith [N_lt_alpha hv hk]

theorem NO_le_A0 (hk : Checks5 c z) : z.N * c.one ≤ z.A0 := le_of_lt hk.hNlo

theorem NO_le_A1 (hv : Valid c t K) (hk : Checks5 c z) : z.N * c.one ≤ z.A1 := by
  have h1 : ((z.N * c.one : ℕ) : ℝ) < z.A0 := by exact_mod_cast hk.hNlo
  have h2 := A0_le hv hk
  have h3 := A1_ge hv hk
  have : ((z.N * c.one : ℕ) : ℝ) ≤ z.A1 := by linarith
  exact_mod_cast this

/-- `p 2^P` lies in `[A0 - N o, A1 - N o]`. -/
theorem p_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (((z.A0 - z.N * c.one : ℕ)) : ℝ) ≤ RSInt.rsFrac t * 2 ^ c.P := by
  rw [Nat.cast_sub (NO_le_A0 hk), frac_eq hv hk]
  push_cast; rw [oneR hv]
  have := A0_le hv hk
  nlinarith

theorem p_hi (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t * 2 ^ c.P ≤ (((z.A1 - z.N * c.one : ℕ)) : ℝ) := by
  rw [Nat.cast_sub (NO_le_A1 hv hk), frac_eq hv hk]
  push_cast; rw [oneR hv]
  have := A1_ge hv hk
  nlinarith

theorem N_pos (hk : Checks5 c z) : (0 : ℝ) < z.N := by
  have := hk.hN; exact_mod_cast this

/-- `y = p / N` bracket. -/
theorem y_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.Y0 : ℝ) ≤ RSInt.rsFrac t / z.N * 2 ^ c.P := by
  have hN := N_pos hk
  have h : ((z.Y0 * z.N : ℕ) : ℝ) ≤ ((z.A0 - z.N * c.one : ℕ) : ℝ) := by exact_mod_cast hk.hY0
  have hp := p_lo hv hk
  push_cast at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hN]
  linarith

theorem y_hi (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t / z.N * 2 ^ c.P ≤ (z.Y1 : ℝ) := by
  have hN := N_pos hk
  have h : ((z.A1 - z.N * c.one : ℕ) : ℝ) ≤ ((z.Y1 * z.N : ℕ) : ℝ) := by exact_mod_cast hk.hY1
  have hp := p_hi hv hk
  push_cast at h
  rw [div_mul_eq_mul_div, div_le_iff₀ hN]
  linarith

theorem y_nonneg (hv : Valid c t K) (hk : Checks5 c z) : 0 ≤ RSInt.rsFrac t / z.N :=
  div_nonneg (frac_pos hv hk).le (N_pos hk).le

theorem y_le_half (hv : Valid c t K) (hk : Checks5 c z) : RSInt.rsFrac t / z.N ≤ 1 / 2 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((2 * z.Y1 : ℕ) : ℝ) ≤ (c.one : ℝ) := by exact_mod_cast hk.hYhalf
  push_cast at h; rw [oneR hv] at h
  have := y_hi hv hk
  by_contra hc; rw [not_le] at hc
  nlinarith

/-- `a = N (1 + y)`, hence `log a = log N + log (1 + y)`. -/
theorem log_alpha (hv : Valid c t K) (hk : Checks5 c z) :
    Real.log (RSInt.rsAlpha t) = Real.log (z.N : ℝ) + Real.log (1 + RSInt.rsFrac t / z.N) := by
  have hN := N_pos hk
  have hy := y_nonneg hv hk
  rw [← Real.log_mul hN.ne' (by linarith)]
  congr 1
  rw [frac_eq hv hk]; field_simp; ring

/-- `LG0 <= log (1 + y) 2^P <= LG1`. -/
theorem lg_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.LG0 : ℝ) ≤ Real.log (1 + RSInt.rsFrac t / z.N) * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have ho : 0 < c.one := by rw [hv.one_eq]; positivity
  set y := RSInt.rsFrac t / z.N with hydef
  set y0 : ℝ := (z.Y0 : ℝ) / 2 ^ c.P with hy0
  have hy0le : y0 ≤ y := by rw [hy0, div_le_iff₀ hP]; exact y_lo hv hk
  have hy00 : 0 ≤ y0 := by positivity
  have hyh := y_le_half hv hk
  have hmono : Real.log (1 + y0) ≤ Real.log (1 + y) :=
    Real.log_le_log (by linarith) (by linarith)
  have hser := log_one_add_near hy00 (by linarith)
  rw [abs_le] at hser
  have h : ((z.LG0 * 840 * c.one ^ 8 + 1680 * z.Y0 ^ 9 + lpNeg z.Y0 c.one : ℕ) : ℝ)
      ≤ ((lpPos z.Y0 c.one : ℕ) : ℝ) := by exact_mod_cast hk.hLG0
  have hl := lp_real z.Y0 c.one ho
  rw [oneR hv] at hl
  push_cast at h
  rw [oneR hv] at h
  -- h : LG0 840 O^8 + 1680 Y0^9 + neg <= pos ; hl : pos - neg = 840 O^9 L(y0)
  have hY : (z.Y0 : ℝ) = y0 * 2 ^ c.P := by rw [hy0]; field_simp
  rw [← hy0] at hl
  have h2 : (z.LG0 : ℝ) * 840 * (2 ^ c.P) ^ 8 + 1680 * (y0 * 2 ^ c.P) ^ 9
      ≤ 840 * (2 ^ c.P) ^ 9 * Lser y0 := by rw [← hY]; linarith
  have h3 : (z.LG0 : ℝ) ≤ (Lser y0 - 2 * y0 ^ 9) * 2 ^ c.P := by
    have hO8 : (0 : ℝ) < 840 * (2 ^ c.P) ^ 8 := by positivity
    rw [← mul_le_mul_iff_left₀ hO8]
    have e : (Lser y0 - 2 * y0 ^ 9) * 2 ^ c.P * (840 * (2 ^ c.P) ^ 8)
        = 840 * (2 ^ c.P) ^ 9 * Lser y0 - 1680 * (y0 * 2 ^ c.P) ^ 9 := by ring
    rw [e]; linarith
  have h4 : (Lser y0 - 2 * y0 ^ 9) * 2 ^ c.P ≤ Real.log (1 + y) * 2 ^ c.P :=
    mul_le_mul_of_nonneg_right (by linarith [hser.2]) hP.le
  linarith

theorem lg_hi (hv : Valid c t K) (hk : Checks5 c z) :
    Real.log (1 + RSInt.rsFrac t / z.N) * 2 ^ c.P ≤ (z.LG1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have ho : 0 < c.one := by rw [hv.one_eq]; positivity
  set y := RSInt.rsFrac t / z.N with hydef
  set y1 : ℝ := (z.Y1 : ℝ) / 2 ^ c.P with hy1
  have hyle : y ≤ y1 := by rw [hy1, le_div_iff₀ hP]; exact y_hi hv hk
  have hy0 := y_nonneg hv hk
  have hy1h : y1 ≤ 1 / 2 := by
    have h : ((2 * z.Y1 : ℕ) : ℝ) ≤ (c.one : ℝ) := by exact_mod_cast hk.hYhalf
    push_cast at h; rw [oneR hv] at h
    rw [hy1, div_le_iff₀ hP]; linarith
  have hmono : Real.log (1 + y) ≤ Real.log (1 + y1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hser := log_one_add_near (by linarith : 0 ≤ y1) hy1h
  rw [abs_le] at hser
  have h : ((lpPos z.Y1 c.one + 1680 * z.Y1 ^ 9 : ℕ) : ℝ)
      ≤ ((z.LG1 * 840 * c.one ^ 8 + lpNeg z.Y1 c.one : ℕ) : ℝ) := by exact_mod_cast hk.hLG1
  have hl := lp_real z.Y1 c.one ho
  rw [oneR hv] at hl
  push_cast at h
  rw [oneR hv] at h
  have hY : (z.Y1 : ℝ) = y1 * 2 ^ c.P := by rw [hy1]; field_simp
  rw [← hy1] at hl
  have h2 : 840 * (2 ^ c.P) ^ 9 * Lser y1 + 1680 * (y1 * 2 ^ c.P) ^ 9
      ≤ (z.LG1 : ℝ) * 840 * (2 ^ c.P) ^ 8 := by rw [← hY]; linarith
  have h3 : (Lser y1 + 2 * y1 ^ 9) * 2 ^ c.P ≤ (z.LG1 : ℝ) := by
    have hO8 : (0 : ℝ) < 840 * (2 ^ c.P) ^ 8 := by positivity
    rw [← mul_le_mul_iff_left₀ hO8]
    have e : (Lser y1 + 2 * y1 ^ 9) * 2 ^ c.P * (840 * (2 ^ c.P) ^ 8)
        = 840 * (2 ^ c.P) ^ 9 * Lser y1 + 1680 * (y1 * 2 ^ c.P) ^ 9 := by ring
    rw [e]; linarith
  have h4 : Real.log (1 + y) * 2 ^ c.P ≤ (Lser y1 + 2 * y1 ^ 9) * 2 ^ c.P :=
    mul_le_mul_of_nonneg_right (by linarith [hser.1]) hP.le
  linarith

/-! ## 2. the Dirichlet state: `psum t N` and `log N` -/

theorem dstate_inv (hv : Valid c t K) (hk : Checks5 c z) : Inv c t z.N (dstate c z) := by
  have h := run_sound c t K hv (z.N - 1) 1 (St.init c) (inv_init c t hv.one_eq)
  have hN := hk.hN
  rwa [show 1 + (z.N - 1) = z.N by omega] at h

theorem loga_lo (hv : Valid c t K) (hk : Checks5 c z) :
    ((dstate c z).llo : ℝ) + z.LG0 ≤ Real.log (RSInt.rsAlpha t) * 2 ^ c.P := by
  obtain ⟨_, _, h1, _, _, _⟩ := dstate_inv hv hk
  rw [log_alpha hv hk]
  have := lg_lo hv hk
  nlinarith

theorem loga_hi (hv : Valid c t K) (hk : Checks5 c z) :
    Real.log (RSInt.rsAlpha t) * 2 ^ c.P ≤ ((dstate c z).lhi : ℝ) + z.LG1 := by
  obtain ⟨_, _, _, h2, _, _⟩ := dstate_inv hv hk
  rw [log_alpha hv hk]
  have := lg_hi hv hk
  nlinarith

/-! ## 3. the phase ball -/

theorem thetaMain_eq (ht : 0 < t) :
    RSInt.rsThetaMain t = t * Real.log (RSInt.rsAlpha t) - t / 2 - π / 8 := by
  unfold RSInt.rsThetaMain RSInt.rsAlpha
  rw [Real.log_sqrt (by positivity), Real.log_div ht.ne' (by positivity)]
  ring

/-- The scaled phase identity used for both ends of the ball. -/
theorem phase_scaled (t T Q La O s : ℝ) (hT : 0 < T) (hQ : 0 < Q) (ht : t = T / Q) :
    (t * La - t / 2 - π / 8 + s / t) * O * (4 * T * Q)
      = 4 * T ^ 2 * (La * O) - 2 * T ^ 2 * O - (π / 2 * O) * T * Q + s * 4 * O * Q ^ 2 := by
  subst ht
  field_simp
  ring

theorem tn_pos (hk : Checks5 c z) : (0 : ℝ) < c.tn := by
  have h : ((509 * 2 ^ c.tq : ℕ) : ℝ) ≤ c.tn := by exact_mod_cast hk.ht
  push_cast at h
  have : (0 : ℝ) < 509 * 2 ^ c.tq := by positivity
  linarith

theorem phase_lo (hv : Valid c t K) (hk : Checks5 c z) {φ : ℝ}
    (hφ : |φ - RSInt.rsThetaMain t| ≤ 1 / t) : (z.TH0 : ℝ) ≤ φ * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hQ : (0 : ℝ) < 2 ^ c.tq := by positivity
  have hT := tn_pos hk
  have ht := t_pos hv hk
  have h : ((z.TH0 * (4 * c.tn * 2 ^ c.tq) + 2 * c.tn * c.tn * c.one + c.tn * 2 ^ c.tq * (c.hp + c.rp)
      + 4 * c.one * 2 ^ c.tq * 2 ^ c.tq : ℕ) : ℝ)
      ≤ ((4 * c.tn * c.tn * ((dstate c z).llo + z.LG0) : ℕ) : ℝ) := by exact_mod_cast hk.hTH0
  push_cast at h
  rw [oneR hv] at h
  have hL := loga_lo hv hk
  have hpi := pi_hi hv
  have hφ' : RSInt.rsThetaMain t + (-1) / t ≤ φ := by
    have := (abs_le.mp hφ).1; rw [neg_div]; linarith
  rw [thetaMain_eq ht] at hφ'
  have e := phase_scaled t c.tn (2 ^ c.tq) (Real.log (RSInt.rsAlpha t)) (2 ^ c.P) (-1) hT hQ hv.t_eq
  have hw : (0 : ℝ) < 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by positivity
  have h1 : (t * Real.log (RSInt.rsAlpha t) - t / 2 - π / 8 + (-1) / t) * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq)
      ≤ φ * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by
    rw [mul_assoc, mul_assoc φ]; exact mul_le_mul_of_nonneg_right hφ' hw.le
  have h2 : 4 * (c.tn : ℝ) ^ 2 * (((dstate c z).llo : ℝ) + z.LG0)
      ≤ 4 * (c.tn : ℝ) ^ 2 * (Real.log (RSInt.rsAlpha t) * 2 ^ c.P) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h3 : (π / 2 * 2 ^ c.P) * c.tn * 2 ^ c.tq ≤ ((c.hp : ℝ) + c.rp) * c.tn * 2 ^ c.tq := by
    apply mul_le_mul_of_nonneg_right _ hQ.le
    exact mul_le_mul_of_nonneg_right hpi hT.le
  have h4 : (z.TH0 : ℝ) * (4 * c.tn * 2 ^ c.tq) ≤ φ * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by
    nlinarith
  exact le_of_mul_le_mul_right h4 (by positivity)

theorem phase_hi (hv : Valid c t K) (hk : Checks5 c z) {φ : ℝ}
    (hφ : |φ - RSInt.rsThetaMain t| ≤ 1 / t) : φ * 2 ^ c.P ≤ (z.TH1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hQ : (0 : ℝ) < 2 ^ c.tq := by positivity
  have hT := tn_pos hk
  have ht := t_pos hv hk
  have h : ((4 * c.tn * c.tn * ((dstate c z).lhi + z.LG1) + 4 * c.one * 2 ^ c.tq * 2 ^ c.tq : ℕ) : ℝ)
      ≤ ((z.TH1 * (4 * c.tn * 2 ^ c.tq) + 2 * c.tn * c.tn * c.one
          + c.tn * 2 ^ c.tq * (c.hp - c.rp) : ℕ) : ℝ) := by exact_mod_cast hk.hTH1
  push_cast [Nat.cast_sub hk.hrp] at h
  rw [oneR hv] at h
  have hL := loga_hi hv hk
  have hpi := pi_lo hv
  have hφ' : φ ≤ RSInt.rsThetaMain t + 1 / t := by
    have := (abs_le.mp hφ).2; linarith
  rw [thetaMain_eq ht] at hφ'
  have e := phase_scaled t c.tn (2 ^ c.tq) (Real.log (RSInt.rsAlpha t)) (2 ^ c.P) 1 hT hQ hv.t_eq
  have hw : (0 : ℝ) < 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by positivity
  have h1 : φ * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq)
      ≤ (t * Real.log (RSInt.rsAlpha t) - t / 2 - π / 8 + 1 / t) * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) := by
    rw [mul_assoc, mul_assoc (t * Real.log (RSInt.rsAlpha t) - t / 2 - π / 8 + 1 / t)]
    exact mul_le_mul_of_nonneg_right hφ' hw.le
  have h2 : 4 * (c.tn : ℝ) ^ 2 * (Real.log (RSInt.rsAlpha t) * 2 ^ c.P)
      ≤ 4 * (c.tn : ℝ) ^ 2 * (((dstate c z).lhi : ℝ) + z.LG1) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h3 : ((c.hp : ℝ) - c.rp) * c.tn * 2 ^ c.tq ≤ (π / 2 * 2 ^ c.P) * c.tn * 2 ^ c.tq := by
    apply mul_le_mul_of_nonneg_right _ hQ.le
    exact mul_le_mul_of_nonneg_right hpi hT.le
  have h4 : φ * 2 ^ c.P * (4 * c.tn * 2 ^ c.tq) ≤ (z.TH1 : ℝ) * (4 * c.tn * 2 ^ c.tq) := by
    nlinarith
  exact le_of_mul_le_mul_right h4 (by positivity)

/-! ## 4. the C0 amplitude `(t/2pi)^(-1/4) = a^(-1/2)` -/

theorem alpha_pos (hv : Valid c t K) (hk : Checks5 c z) : 0 < RSInt.rsAlpha t := by
  have := N_lt_alpha hv hk; have := N_pos hk; linarith

theorem w_sq_alpha (ht : 0 < t) :
    ((t / (2 * π)) ^ (-(1 / 4 : ℝ))) ^ 2 * RSInt.rsAlpha t = 1 := by
  have hx : (0 : ℝ) < t / (2 * π) := by positivity
  have ha : 0 < RSInt.rsAlpha t := Real.sqrt_pos.mpr hx
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  unfold RSInt.rsAlpha
  field_simp

theorem w_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.Q0 : ℝ) ≤ (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have ht := t_pos hv hk
  have ha := alpha_pos hv hk
  have hwa := w_sq_alpha ht
  set w := (t / (2 * π)) ^ (-(1 / 4 : ℝ)) with hwdef
  have hw : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have h : ((z.Q0 * z.Q0 * z.A1 : ℕ) : ℝ) ≤ ((c.one * c.one * c.one : ℕ) : ℝ) := by
    exact_mod_cast hk.hQ0
  push_cast at h; rw [oneR hv] at h
  have hA1 := A1_ge hv hk
  have h1 : (z.Q0 : ℝ) ^ 2 * (RSInt.rsAlpha t * 2 ^ c.P) ≤ (z.Q0 : ℝ) ^ 2 * z.A1 :=
    mul_le_mul_of_nonneg_left hA1 (by positivity)
  have h2 : (z.Q0 : ℝ) ^ 2 * RSInt.rsAlpha t ≤ (w * 2 ^ c.P) ^ 2 * RSInt.rsAlpha t := by
    have e : (w * 2 ^ c.P) ^ 2 * RSInt.rsAlpha t = (2 ^ c.P) ^ 2 := by
      rw [mul_pow, mul_comm (w ^ 2), mul_assoc, hwa, mul_one]
    rw [e]
    have : (z.Q0 : ℝ) ^ 2 * RSInt.rsAlpha t * 2 ^ c.P ≤ (2 ^ c.P) ^ 2 * 2 ^ c.P := by nlinarith
    exact le_of_mul_le_mul_right this hP
  have h3 : (z.Q0 : ℝ) ^ 2 ≤ (w * 2 ^ c.P) ^ 2 := le_of_mul_le_mul_right h2 ha
  by_contra hc
  simp only [not_le] at hc
  have := pow_lt_pow_left₀ hc (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
  linarith

theorem w_hi (hv : Valid c t K) (hk : Checks5 c z) :
    (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * 2 ^ c.P ≤ (z.Q1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have ht := t_pos hv hk
  have ha := alpha_pos hv hk
  have hwa := w_sq_alpha ht
  set w := (t / (2 * π)) ^ (-(1 / 4 : ℝ)) with hwdef
  have hw : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have h : ((c.one * c.one * c.one : ℕ) : ℝ) ≤ ((z.Q1 * z.Q1 * z.A0 : ℕ) : ℝ) := by
    exact_mod_cast hk.hQ1
  push_cast at h; rw [oneR hv] at h
  have hA0 := A0_le hv hk
  have h1 : (z.Q1 : ℝ) ^ 2 * z.A0 ≤ (z.Q1 : ℝ) ^ 2 * (RSInt.rsAlpha t * 2 ^ c.P) :=
    mul_le_mul_of_nonneg_left hA0 (by positivity)
  have h2 : (w * 2 ^ c.P) ^ 2 * RSInt.rsAlpha t ≤ (z.Q1 : ℝ) ^ 2 * RSInt.rsAlpha t := by
    have e : (w * 2 ^ c.P) ^ 2 * RSInt.rsAlpha t = (2 ^ c.P) ^ 2 := by
      rw [mul_pow, mul_comm (w ^ 2), mul_assoc, hwa, mul_one]
    rw [e]
    have : (2 ^ c.P) ^ 2 * 2 ^ c.P ≤ (z.Q1 : ℝ) ^ 2 * RSInt.rsAlpha t * 2 ^ c.P := by nlinarith
    exact le_of_mul_le_mul_right this hP
  have h3 : (w * 2 ^ c.P) ^ 2 ≤ (z.Q1 : ℝ) ^ 2 := le_of_mul_le_mul_right h2 ha
  by_contra hc
  simp only [not_le] at hc
  have := pow_lt_pow_left₀ hc (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
  linarith

/-! ## 5. the angles `2 pi p` and `2 pi (p - p^2 + 1/16)` -/

theorem U_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.U0 : ℝ) ≤ 2 * π * RSInt.rsFrac t * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((z.U0 * c.one : ℕ) : ℝ) ≤ ((4 * (c.hp - c.rp) * (z.A0 - z.N * c.one) : ℕ) : ℝ) := by
    exact_mod_cast hk.hU0
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk.hrp, oneR hv] at h
  have hp := p_lo hv hk
  have hpi := pi_lo hv
  have hr : (0 : ℝ) ≤ (c.hp : ℝ) - c.rp := by
    have : (c.rp : ℝ) ≤ c.hp := by exact_mod_cast hk.hrp
    linarith
  have h1 : ((c.hp : ℝ) - c.rp) * ((z.A0 - z.N * c.one : ℕ) : ℝ)
      ≤ (π / 2 * 2 ^ c.P) * (RSInt.rsFrac t * 2 ^ c.P) :=
    mul_le_mul hpi hp (by positivity) (by positivity)
  have h2 : (z.U0 : ℝ) * 2 ^ c.P ≤ (2 * π * RSInt.rsFrac t * 2 ^ c.P) * 2 ^ c.P := by
    push_cast at h; nlinarith
  exact le_of_mul_le_mul_right h2 hP

theorem U_hi (hv : Valid c t K) (hk : Checks5 c z) :
    2 * π * RSInt.rsFrac t * 2 ^ c.P ≤ (z.U1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((4 * (c.hp + c.rp) * (z.A1 - z.N * c.one) : ℕ) : ℝ) ≤ ((z.U1 * c.one : ℕ) : ℝ) := by
    exact_mod_cast hk.hU1
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, oneR hv] at h
  have hp := p_hi hv hk
  have hpi := pi_hi hv
  have hf := frac_pos hv hk
  have h1 : (π / 2 * 2 ^ c.P) * (RSInt.rsFrac t * 2 ^ c.P)
      ≤ ((c.hp : ℝ) + c.rp) * ((z.A1 - z.N * c.one : ℕ) : ℝ) :=
    mul_le_mul hpi hp (by positivity) (by positivity)
  have h2 : (2 * π * RSInt.rsFrac t * 2 ^ c.P) * 2 ^ c.P ≤ (z.U1 : ℝ) * 2 ^ c.P := by
    push_cast at h; nlinarith
  exact le_of_mul_le_mul_right h2 hP

/-- The numerator angle `v = 2 pi (p - p^2 + 1/16)`. -/
def vAng (p : ℝ) : ℝ := 2 * π * (p - p ^ 2 + 1 / 16)

theorem G_bounds (hv : Valid c t K) (hk : Checks5 c z) :
    (((16 * (z.A0 - z.N * c.one) * c.one + c.one * c.one
        - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one) : ℕ)) : ℝ)
      ≤ 16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2 ∧
    16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2
      ≤ 16 * ((z.A1 - z.N * c.one : ℕ) : ℝ) * 2 ^ c.P + (2 ^ c.P) ^ 2
        - 16 * ((z.A0 - z.N * c.one : ℕ) : ℝ) ^ 2 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hlo := p_lo hv hk
  have hhi := p_hi hv hk
  have hf := frac_pos hv hk
  set x := RSInt.rsFrac t * 2 ^ c.P with hx
  have e : 16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2
      = 16 * x * 2 ^ c.P - 16 * x ^ 2 + (2 ^ c.P) ^ 2 := by rw [hx]; ring
  rw [e]
  have hx0 : 0 ≤ x := by positivity
  have hP0 : (0 : ℝ) ≤ ((z.A0 - z.N * c.one : ℕ) : ℝ) := by positivity
  constructor
  · rw [Nat.cast_sub hk.hG0]
    push_cast [Nat.cast_sub (NO_le_A0 hk), Nat.cast_sub (NO_le_A1 hv hk)]
    rw [oneR hv]
    push_cast [Nat.cast_sub (NO_le_A0 hk), Nat.cast_sub (NO_le_A1 hv hk), oneR hv] at hlo hhi
    nlinarith
  · have h1 : ((z.A0 - z.N * c.one : ℕ) : ℝ) ^ 2 ≤ x ^ 2 := by
      apply pow_le_pow_left₀ hP0 hlo
    nlinarith

theorem V_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.V0 : ℝ) ≤ vAng (RSInt.rsFrac t) * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  obtain ⟨hG, _⟩ := G_bounds hv hk
  have h : ((z.V0 * (4 * c.one * c.one) : ℕ) : ℝ) ≤ (((c.hp - c.rp) * (16 * (z.A0 - z.N * c.one) * c.one
      + c.one * c.one - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one)) : ℕ) : ℝ) := by
    exact_mod_cast hk.hV0
  rw [Nat.cast_mul, Nat.cast_mul (c.hp - c.rp), Nat.cast_sub hk.hrp] at h
  have hpi := pi_lo hv
  have hr : (0 : ℝ) ≤ (c.hp : ℝ) - c.rp := by
    have : (c.rp : ℝ) ≤ c.hp := by exact_mod_cast hk.hrp
    linarith
  have hG0 : (0 : ℝ) ≤ (((16 * (z.A0 - z.N * c.one) * c.one + c.one * c.one
        - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one) : ℕ)) : ℝ) := by positivity
  have h1 := mul_le_mul hpi hG hG0 (by positivity)
  have e : (π / 2 * 2 ^ c.P) * (16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2)
      = (vAng (RSInt.rsFrac t) * 2 ^ c.P) * (4 * 2 ^ c.P * 2 ^ c.P) := by unfold vAng; ring
  rw [e] at h1
  push_cast at h
  rw [oneR hv] at h
  have h2 : (z.V0 : ℝ) * (4 * 2 ^ c.P * 2 ^ c.P) ≤ (vAng (RSInt.rsFrac t) * 2 ^ c.P) * (4 * 2 ^ c.P * 2 ^ c.P) := by
    linarith
  exact le_of_mul_le_mul_right h2 (by positivity)

theorem V_hi (hv : Valid c t K) (hk : Checks5 c z) :
    vAng (RSInt.rsFrac t) * 2 ^ c.P ≤ (z.V1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  obtain ⟨hG, hG'⟩ := G_bounds hv hk
  have h : (((c.hp + c.rp) * (16 * (z.A1 - z.N * c.one) * c.one + c.one * c.one) : ℕ) : ℝ)
      ≤ ((z.V1 * (4 * c.one * c.one) + (c.hp + c.rp) * (16 * (z.A0 - z.N * c.one)
          * (z.A0 - z.N * c.one)) : ℕ) : ℝ) := by exact_mod_cast hk.hV1
  push_cast at h
  rw [oneR hv] at h
  have hpi := pi_hi hv
  have hG0 : (0 : ℝ) ≤ (((16 * (z.A0 - z.N * c.one) * c.one + c.one * c.one
        - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one) : ℕ)) : ℝ) := by positivity
  have hg : 0 ≤ 16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2 := le_trans hG0 hG
  have h1 := mul_le_mul hpi hG' hg (by positivity)
  have e : (π / 2 * 2 ^ c.P) * (16 * (RSInt.rsFrac t - RSInt.rsFrac t ^ 2 + 1 / 16) * (2 ^ c.P) ^ 2)
      = (vAng (RSInt.rsFrac t) * 2 ^ c.P) * (4 * 2 ^ c.P * 2 ^ c.P) := by unfold vAng; ring
  rw [e] at h1
  have h2 : (vAng (RSInt.rsFrac t) * 2 ^ c.P) * (4 * 2 ^ c.P * 2 ^ c.P) ≤ (z.V1 : ℝ) * (4 * 2 ^ c.P * 2 ^ c.P) := by
    nlinarith
  exact le_of_mul_le_mul_right h2 (by positivity)

theorem psi_num_eq (p : ℝ) : Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) = Real.cos (vAng p) := by
  rw [← Real.cos_neg]; unfold vAng; congr 1; ring

end Facts

/-! ## 6. the quotient `Psi = cos v / cos 2 pi p` (denominator bounded away from 0) -/

theorem lin_le_max {F l u y : ℝ} (hl : l ≤ y) (hu : y ≤ u) : F * y ≤ F * l ∨ F * y ≤ F * u := by
  rcases le_total 0 F with hF | hF
  · exact Or.inr (mul_le_mul_of_nonneg_left hu hF)
  · exact Or.inl (mul_le_mul_of_nonpos_left hl hF)

theorem lin_ge_min {F l u y : ℝ} (hl : l ≤ y) (hu : y ≤ u) : F * l ≤ F * y ∨ F * u ≤ F * y := by
  rcases le_total 0 F with hF | hF
  · exact Or.inl (mul_le_mul_of_nonneg_left hl hF)
  · exact Or.inr (mul_le_mul_of_nonpos_left hu hF)

theorem quot_sound {o : ℕ} {O X Y : ℝ} {Nm D F0 F1 : ℤ} {rN rD : ℕ} (hO : (o : ℝ) = O)
    (hOp : 0 < O) (hX : |X * O - Nm| ≤ rN) (hY : |Y * O - D| ≤ rD)
    (hq : QuotOK o Nm rN D rD F0 F1) :
    Y ≠ 0 ∧ (F0 : ℝ) ≤ X / Y * O ∧ X / Y * O ≤ F1 := by
  rw [abs_le] at hX hY
  have eq : X / Y * O = (X * O) * O / (Y * O) := by
    by_cases hY0 : Y = 0
    · simp [hY0]
    · field_simp
  rcases hq with ⟨hD, a1, a2, a3, a4⟩ | ⟨hD, a1, a2, a3, a4⟩
  · have hD' : ((rD : ℤ) : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have a1' : ((F0 * (D - rD) : ℤ) : ℝ) ≤ (((Nm - rN) * o : ℤ) : ℝ) := by exact_mod_cast a1
    have a2' : ((F0 * (D + rD) : ℤ) : ℝ) ≤ (((Nm - rN) * o : ℤ) : ℝ) := by exact_mod_cast a2
    have a3' : (((Nm + rN) * o : ℤ) : ℝ) ≤ ((F1 * (D - rD) : ℤ) : ℝ) := by exact_mod_cast a3
    have a4' : (((Nm + rN) * o : ℤ) : ℝ) ≤ ((F1 * (D + rD) : ℤ) : ℝ) := by exact_mod_cast a4
    push_cast at hD' a1' a2' a3' a4'
    rw [hO] at a1' a2' a3' a4'
    have hYp : 0 < Y * O := by linarith
    have hY0 : Y ≠ 0 := by
      intro h; rw [h, zero_mul] at hYp; exact lt_irrefl _ hYp
    refine ⟨hY0, ?_, ?_⟩
    · rw [eq, le_div_iff₀ hYp]
      have hxo : ((Nm : ℝ) - rN) * O ≤ (X * O) * O := mul_le_mul_of_nonneg_right (by linarith [hX.1]) hOp.le
      rcases lin_le_max (F := (F0 : ℝ)) hY.1 hY.2 with h | h <;> nlinarith
    · rw [eq, div_le_iff₀ hYp]
      have hxo : (X * O) * O ≤ ((Nm : ℝ) + rN) * O := mul_le_mul_of_nonneg_right (by linarith [hX.2]) hOp.le
      rcases lin_ge_min (F := (F1 : ℝ)) hY.1 hY.2 with h | h <;> nlinarith
  · have hD' : (D : ℝ) + ((rD : ℤ) : ℝ) < 0 := by exact_mod_cast hD
    have a1' : (((Nm + rN) * o : ℤ) : ℝ) ≤ ((F0 * (D - rD) : ℤ) : ℝ) := by exact_mod_cast a1
    have a2' : (((Nm + rN) * o : ℤ) : ℝ) ≤ ((F0 * (D + rD) : ℤ) : ℝ) := by exact_mod_cast a2
    have a3' : ((F1 * (D - rD) : ℤ) : ℝ) ≤ (((Nm - rN) * o : ℤ) : ℝ) := by exact_mod_cast a3
    have a4' : ((F1 * (D + rD) : ℤ) : ℝ) ≤ (((Nm - rN) * o : ℤ) : ℝ) := by exact_mod_cast a4
    push_cast at hD' a1' a2' a3' a4'
    rw [hO] at a1' a2' a3' a4'
    have hYn : Y * O < 0 := by linarith
    have hY0 : Y ≠ 0 := by
      intro h; rw [h, zero_mul] at hYn; exact lt_irrefl _ hYn
    refine ⟨hY0, ?_, ?_⟩
    · rw [eq, le_div_iff_of_neg hYn]
      have hxo : (X * O) * O ≤ ((Nm : ℝ) + rN) * O := mul_le_mul_of_nonneg_right (by linarith [hX.2]) hOp.le
      rcases lin_ge_min (F := (F0 : ℝ)) hY.1 hY.2 with h | h <;> nlinarith
    · rw [eq, div_le_iff_of_neg hYn]
      have hxo : ((Nm : ℝ) - rN) * O ≤ (X * O) * O := mul_le_mul_of_nonneg_right (by linarith [hX.1]) hOp.le
      rcases lin_le_max (F := (F1 : ℝ)) hY.1 hY.2 with h | h <;> nlinarith

/-! ## 7. the main sum as `Re (e^{i phi} psum t N)` -/

theorem main_sum_eq (t φ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n)
      = Real.cos φ * (psum t N).re - Real.sin φ * (psum t N).im := by
  unfold psum
  rw [Complex.re_sum, Complex.im_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.Ico_add_one_right_eq_Icc]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 0 < n := (Finset.mem_Icc.mp hn).1
  obtain ⟨h1, h2⟩ := cpow_term n hn1 t
  rw [h1, h2, Real.cos_sub]
  have : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [this]
  ring

/-! ## 8. the DIntv assembly -/

section Assembly

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}

theorem mainBox_mem (hv : Valid c t K) (hk : Checks5 c z) {φ : ℝ}
    (hφ : |φ - RSInt.rsThetaMain t| ≤ 1 / t) :
    (mainBox c z).memR (2 * (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im)) := by
  obtain ⟨_, _, _, _, hre, him⟩ := dstate_inv hv hk
  obtain ⟨hc, hs, _, _⟩ := trig_sound c t K hv φ z.TH0 z.TH1 (phase_lo hv hk hφ) (phase_hi hv hk hφ)
  unfold SBall at hc hs
  rw [← sgnI_cast] at hc hs
  have mre : (ballD c.P (((dstate c z).reP : ℤ) - (dstate c z).reN) (dstate c z).reR).memR
      (psum t z.N).re := ballD_mem (by push_cast; exact hre)
  have mim : (ballD c.P (((dstate c z).imP : ℤ) - (dstate c z).imN) (dstate c z).imR).memR
      (psum t z.N).im := ballD_mem (by push_cast; exact him)
  have mc : (ballD c.P (sgnI (phTrig c z).cs (phTrig c z).cm) (phTrig c z).cr).memR (Real.cos φ) :=
    ballD_mem hc
  have ms : (ballD c.P (sgnI (phTrig c z).ss (phTrig c z).sm) (phTrig c z).sr).memR (Real.sin φ) :=
    ballD_mem hs
  have m1 := DIntv.sub_sound (by rfl) (DIntv.mul_sound mc mre) (DIntv.mul_sound ms mim)
  have m2 := DIntv.add_sound (by rfl) m1 m1
  rw [show 2 * (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im)
      = (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im)
        + (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im) by ring]
  exact m2

theorem neg_one_pow_eq (N : ℕ) :
    (-1 : ℝ) ^ (N + 1) = if (N % 2 == 1) = true then 1 else -1 := by
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · have hE : Even N := Nat.even_iff.mpr h
    rw [pow_succ, hE.neg_one_pow]
    simp [h]
  · have hO : Odd N := Nat.odd_iff.mpr h
    rw [pow_succ, hO.neg_one_pow]
    simp [h]

theorem c0Box_mem {w ψ : ℝ} (hw0 : (z.Q0 : ℝ) ≤ w * 2 ^ c.P) (hw1 : w * 2 ^ c.P ≤ z.Q1)
    (hψ0 : (z.F0 : ℝ) ≤ ψ * 2 ^ c.P) (hψ1 : ψ * 2 ^ c.P ≤ z.F1) :
    (c0Box c z).memR ((-1 : ℝ) ^ (z.N + 1) * w * ψ) := by
  have mw : DIntv.memR w ⟨(z.Q0 : ℤ), (z.Q1 : ℤ), -(c.P : ℤ)⟩ :=
    brD_mem (by exact_mod_cast hw0) (by exact_mod_cast hw1)
  have mψ : DIntv.memR ψ ⟨z.F0, z.F1, -(c.P : ℤ)⟩ := brD_mem hψ0 hψ1
  have m := negIf_mem (z.N % 2 == 1) (DIntv.mul_sound mw mψ)
  rw [neg_one_pow_eq]
  unfold c0Box
  split_ifs at m ⊢ with h
  · simpa using m
  · simpa using m

theorem zBox_e (c : Cfg) (z : Cert) : (zBox c z).e = -(c.P : ℤ) + -(c.P : ℤ) := rfl

end Assembly

/-! ## 9. THE SOUNDNESS THEOREM -/

/-- **Soundness of the t >= 509 Riemann-Siegel main-term checker (lane B5; the proof is lane B4's `RS4.check_sound` verbatim with the floor 509).**  If the kernel accepts
    `(c, z)` for a configuration valid at height `t`, then `t >= 509`, the Riemann-Siegel
    length is `z.N`, the fractional part is positive, `cos (2 pi p) ≠ 0`, and for EVERY phase in
    the ball `|phi - thetaMain t| <= 1/t` the main term lies in `[zlo, zhi] / 2^(2P)`. -/
theorem check5_sound {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert)
    (h : check5 c z = true) :
    509 ≤ t ∧ RSInt.rsNn t = z.N ∧ 0 < RSInt.rsFrac t ∧
      Real.cos (2 * π * RSInt.rsFrac t) ≠ 0 ∧
      ∀ φ : ℝ, |φ - RSInt.rsThetaMain t| ≤ 1 / t →
        (z.zlo : ℝ) / 2 ^ (2 * c.P) ≤ Zmain t φ ∧ Zmain t φ ≤ (z.zhi : ℝ) / 2 ^ (2 * c.P) := by
  have hk : Checks5 c z := checks5_of (of_decide_eq_true h)
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hN := N_eq hv hk
  -- the Psi quotient
  obtain ⟨hcU, _, _, _⟩ := trig_sound c t K hv (2 * π * RSInt.rsFrac t) z.U0 z.U1 (U_lo hv hk) (U_hi hv hk)
  obtain ⟨hcV, _, _, _⟩ := trig_sound c t K hv (vAng (RSInt.rsFrac t)) z.V0 z.V1 (V_lo hv hk) (V_hi hv hk)
  unfold SBall at hcU hcV
  rw [← sgnI_cast] at hcU hcV
  obtain ⟨hden, hψ0, hψ1⟩ := quot_sound (oneR hv) hP hcV hcU hk.hPsi
  refine ⟨t_ge hv hk, hN, frac_pos hv hk, hden, ?_⟩
  intro φ hφ
  have hm := mainBox_mem hv hk hφ
  have hc0 := c0Box_mem (c := c) (z := z) (w_lo hv hk) (w_hi hv hk) hψ0 hψ1
  have hz := DIntv.add_sound (by rfl) hm hc0
  have hZ : Zmain t φ = 2 * (Real.cos φ * (psum t z.N).re - Real.sin φ * (psum t z.N).im)
      + (-1 : ℝ) ^ (z.N + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ))
        * (Real.cos (vAng (RSInt.rsFrac t)) / Real.cos (2 * π * RSInt.rsFrac t)) := by
    unfold Zmain RSInt.rsPsi
    rw [hN, main_sum_eq, psi_num_eq]
  rw [hZ]
  change (zBox c z).memR _ at hz
  obtain ⟨hz0, hz1⟩ := hz
  rw [zBox_e] at hz0 hz1
  have e2 : (2 : ℝ) ^ (-(c.P : ℤ) + -(c.P : ℤ)) = 1 / 2 ^ (2 * c.P) := by
    rw [← neg_add, zpow_neg, ← two_mul, zpow_mul, zpow_natCast, one_div]
    norm_cast
    rw [← pow_mul, mul_comm]
  rw [e2] at hz0 hz1
  have hlo : (z.zlo : ℝ) ≤ ((zBox c z).lo : ℝ) := by exact_mod_cast hk.hzlo
  have hhi : ((zBox c z).hi : ℝ) ≤ (z.zhi : ℝ) := by exact_mod_cast hk.hzhi
  have hq : (0 : ℝ) < 1 / 2 ^ (2 * c.P) := by positivity
  constructor
  · calc (z.zlo : ℝ) / 2 ^ (2 * c.P) = (z.zlo : ℝ) * (1 / 2 ^ (2 * c.P)) := by ring
      _ ≤ ((zBox c z).lo : ℝ) * (1 / 2 ^ (2 * c.P)) := mul_le_mul_of_nonneg_right hlo hq.le
      _ ≤ _ := hz0
  · calc _ ≤ ((zBox c z).hi : ℝ) * (1 / 2 ^ (2 * c.P)) := hz1
      _ ≤ (z.zhi : ℝ) * (1 / 2 ^ (2 * c.P)) := mul_le_mul_of_nonneg_right hhi hq.le
      _ = (z.zhi : ℝ) / 2 ^ (2 * c.P) := by ring

end

end RS5
