/-  RS5_Z.lean -- lane B5: the t >= 509 checker `RS5.check5` glued to the SEAM bound
    `RSSeam.rs_Z_C0_seam` (remainder (13/5) t^(-3/4)), and certified signs of one dyadic sample.

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `rs5_Z_enclosure` : `Valid c t K`, `check5 c z = true` give `M > 0`, `phi` with
            Gammaℝ(1/2+it) = M e^{i phi},  |phi - thetaMain t| <= 1/t,
            zlo/2^(2P) - (13/5) t^(-3/4) <= Re completedRiemannZeta(1/2+it) / M
                                         <= zhi/2^(2P) + (13/5) t^(-3/4)
        (the EXACT t-dependent margin of the seam bound; valid from t >= 509).
      * `tpow_le_margin` : `MarginOK c E` (an integer inequality) gives `t^(-3/4) <= E / 2^P`.
      * `rs5_Z_enclosure_E` : the same enclosure with the rational margin `(13/5) E / 2^P`.
      * `rs5_sign_pos` / `rs5_sign_neg` : a box clearing `(13/5) E / 2^P` on one side pins the SIGN of
        `Re completedRiemannZeta(1/2+it)` (= `XiLineZeros.gLine t`).
      * `sampleOK_sign` : a certified `Sample` (`sampleOK s = true`) has the claimed sign of `gLine`
        at `s.t = tn / 2^tq`.

    conjecture1_proved = False.  Finite-height sign certification; nothing about RH.
-/
import RS5_Sound
import RSSeam_Bridge
import EMZetaHighCheck
import SignChain

open Complex
open scoped Real

namespace RS5

open ArbEcon
open RS4 (Cert Zmain)

noncomputable section

/-- **Retargeted enclosure (t >= 509), exact margin `(13/5) t^(-3/4)`.** -/
theorem rs5_Z_enclosure {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert)
    (h : check5 c z = true) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 13 / 5 * t ^ (-(3 / 4 : ℝ)) ≤
        (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤
        (z.zhi : ℝ) / 2 ^ (2 * c.P) + 13 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨ht, _, hp, hcos, hZ⟩ := check5_sound hv z h
  obtain ⟨M, φ, hM, hpol, hφ, hb⟩ := RSSeam.rs_Z_C0_seam ht hp hcos
  refine ⟨M, φ, hM, hpol, hφ, ?_⟩
  have hz := hZ φ hφ
  unfold Zmain at hz
  rw [abs_le] at hb
  constructor <;> linarith [hz.1, hz.2, hb.1, hb.2]

/-- `MarginOK c E` gives the rational upper bound `t^(-3/4) <= E / 2^P`. -/
theorem tpow_le_margin {c : Cfg} {t : ℝ} {K : ℕ} {E : ℕ} (hv : Valid c t K) (ht : 0 < t)
    (hm : MarginOK c E) : t ^ (-(3 / 4 : ℝ)) ≤ (E : ℝ) / 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hQ : (0 : ℝ) < 2 ^ c.tq := by positivity
  have hm' : ((c.one ^ 4 * (2 ^ c.tq) ^ 3 : ℕ) : ℝ) ≤ ((E ^ 4 * c.tn ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hm
  push_cast at hm'
  rw [RS4.oneR hv] at hm'
  have htn : (c.tn : ℝ) = t * 2 ^ c.tq := by
    rw [hv.t_eq]; field_simp
  rw [htn] at hm'
  -- hm' : (2^P)^4 (2^tq)^3 <= E^4 (t 2^tq)^3, i.e. 1 <= (E/2^P)^4 t^3
  have key : 1 ≤ ((E : ℝ) / 2 ^ c.P) ^ 4 * t ^ 3 := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : ((2 : ℝ) ^ c.P) ^ 4 * (2 ^ c.tq) ^ 3 ≤ (E : ℝ) ^ 4 * t ^ 3 * (2 ^ c.tq) ^ 3 := by
      rw [mul_pow] at hm'; linarith
    nlinarith [pow_pos hQ 3]
  set x := t ^ (-(3 / 4 : ℝ)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos ht _
  have hx4 : x ^ 4 * t ^ 3 = 1 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
    exact inv_mul_cancel₀ (by positivity)
  by_contra hlt
  push Not at hlt
  have hE0 : (0 : ℝ) ≤ (E : ℝ) / 2 ^ c.P := by positivity
  have h4 : ((E : ℝ) / 2 ^ c.P) ^ 4 < x ^ 4 := pow_lt_pow_left₀ hlt hE0 (by norm_num)
  have ht3 : 0 < t ^ 3 := by positivity
  nlinarith [mul_lt_mul_of_pos_right h4 ht3]

/-- **Retargeted enclosure with the rational margin `(13/5) E / 2^P`.** -/
theorem rs5_Z_enclosure_E {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (hm : MarginOK c E) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 13 / 5 * ((E : ℝ) / 2 ^ c.P) ≤
        (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤
        (z.zhi : ℝ) / 2 ^ (2 * c.P) + 13 / 5 * ((E : ℝ) / 2 ^ c.P) := by
  obtain ⟨M, φ, hM, hpol, hφ, h1, h2⟩ := rs5_Z_enclosure hv z h
  have ht : (509 : ℝ) ≤ t := (check5_sound hv z h).1
  have hmr := tpow_le_margin hv (by linarith) hm
  exact ⟨M, φ, hM, hpol, hφ, by linarith, by linarith⟩

theorem posOK_real {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) {z : Cert} {E : ℕ}
    (hp : PosOK c z E) : 13 / 5 * ((E : ℝ) / 2 ^ c.P) < (z.zlo : ℝ) / 2 ^ (2 * c.P) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((13 * (E : ℤ) * (c.one : ℤ) : ℤ) : ℝ) < ((5 * z.zlo : ℤ) : ℝ) := by exact_mod_cast hp
  push_cast at h
  rw [RS4.oneR hv] at h
  have e : (z.zlo : ℝ) / 2 ^ (2 * c.P) - 13 / 5 * ((E : ℝ) / 2 ^ c.P)
      = (5 * z.zlo - 13 * E * 2 ^ c.P) / (5 * (2 ^ c.P) ^ 2) := by
    rw [pow_mul']; field_simp
  have : 0 < (5 * (z.zlo : ℝ) - 13 * E * 2 ^ c.P) / (5 * (2 ^ c.P) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

theorem negOK_real {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) {z : Cert} {E : ℕ}
    (hn : NegOK c z E) : (z.zhi : ℝ) / 2 ^ (2 * c.P) < -(13 / 5 * ((E : ℝ) / 2 ^ c.P)) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((5 * z.zhi : ℤ) : ℝ) < ((-(13 * (E : ℤ) * (c.one : ℤ)) : ℤ) : ℝ) := by exact_mod_cast hn
  push_cast at h
  rw [RS4.oneR hv] at h
  have e : -(13 / 5 * ((E : ℝ) / 2 ^ c.P)) - (z.zhi : ℝ) / 2 ^ (2 * c.P)
      = (-(13 * E * 2 ^ c.P) - 5 * z.zhi) / (5 * (2 ^ c.P) ^ 2) := by
    rw [pow_mul']; field_simp
  have : 0 < (-(13 * (E : ℝ) * 2 ^ c.P) - 5 * z.zhi) / (5 * (2 ^ c.P) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

/-- A certified box above `(13/5) E / 2^P` gives `Re completedRiemannZeta(1/2+it) > 0`. -/
theorem rs5_sign_pos {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (hm : MarginOK c E) (hpos : PosOK c z E) :
    0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re := by
  obtain ⟨M, _, hM, _, _, h1, _⟩ := rs5_Z_enclosure_E hv z h hm
  have := posOK_real hv hpos
  have : 0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M := by linarith
  exact (div_pos_iff_of_pos_right hM).mp this

/-- A certified box below `-(13/5) E / 2^P` gives `Re completedRiemannZeta(1/2+it) < 0`. -/
theorem rs5_sign_neg {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (hm : MarginOK c E) (hneg : NegOK c z E) :
    (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re < 0 := by
  obtain ⟨M, _, hM, _, _, _, h2⟩ := rs5_Z_enclosure_E hv z h hm
  have := negOK_real hv hneg
  have : (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M < 0 := by linarith
  by_contra hc
  have := div_nonneg (not_lt.mp hc) hM.le
  linarith

/-! ## one sample -/

/-- The real height of a sample. -/
def Sample.t (s : Sample) : ℝ := (s.tn : ℝ) / 2 ^ s.tq

theorem Sample.valid (s : Sample) : Valid s.cfg s.t 9 := ArbEcon.OrderK.valid64 s.tn s.tq _ rfl

/-- **A certified sample has the claimed sign of `gLine`** (`gLine t = Re Lambda(1/2+it)`). -/
theorem sampleOK_sign {s : Sample} (h : sampleOK s = true) :
    (s.pos = true → 0 < XiLineZeros.gLine s.t) ∧ (s.pos = false → XiLineZeros.gLine s.t < 0) := by
  unfold sampleOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hm⟩, hs⟩ := h
  constructor
  · intro hp
    rw [hp, if_pos rfl, decide_eq_true_eq] at hs
    exact rs5_sign_pos s.valid s.z hc hm hs
  · intro hp
    rw [hp] at hs
    simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hs
    exact rs5_sign_neg s.valid s.z hc hm hs

end

end RS5
