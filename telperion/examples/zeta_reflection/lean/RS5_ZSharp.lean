/-  RS5_ZSharp.lean -- lane B5, RSC0 Phase 3: the t >= 509 checker `RS5.check5` glued to the SHARPENED
    bound `RSInt.rs_Z_C0'` (remainder (3/5) t^(-3/4), t >= 4250; RS_BridgeSharp), and certified signs of
    one dyadic sample under `RS5.sampleOK'`.  Variants BESIDE `RS5_Z` (imported read-only).

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `rs5_Z_enclosure'` : `Valid c t K`, `check5 c z = true`, `4250 <= t` give the enclosure of
        `Re completedRiemannZeta(1/2+it) / M` by the box widened by `(3/5) t^(-3/4)`;
      * `rs5_Z_enclosure_E'` : the same with the rational margin `(3/5) E / 2^P` (`MarginOK`);
      * `posOK'_real` / `negOK'_real` : the integer tests `PosOK'` / `NegOK'` cast to reals;
      * `rs5_sign_pos'` / `rs5_sign_neg'` and `sampleOK'_sign` : a sample accepted by `sampleOK'` has the
        claimed sign of `gLine` at `s.t`.

    conjecture1_proved = False.  Finite-height sign certification; nothing about RH.
-/
import RS5_EvalSharp
import RS5_Z
import RS_BridgeSharp

open Complex
open scoped Real

namespace RS5

open ArbEcon
open RS4 (Cert Zmain)

noncomputable section

/-- **Enclosure from the sharpened bound (t >= 4250), exact margin `(3/5) t^(-3/4)`.** -/
theorem rs5_Z_enclosure' {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert)
    (h : check5 c z = true) (ht4 : 4250 ≤ t) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 3 / 5 * t ^ (-(3 / 4 : ℝ)) ≤
        (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤
        (z.zhi : ℝ) / 2 ^ (2 * c.P) + 3 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨_, _, hp, hcos, hZ⟩ := check5_sound hv z h
  obtain ⟨M, φ, hM, hpol, hφ, hb⟩ := RSInt.rs_Z_C0' ht4 hp hcos
  refine ⟨M, φ, hM, hpol, hφ, ?_⟩
  have hz := hZ φ hφ
  unfold Zmain at hz
  rw [abs_le] at hb
  constructor <;> linarith [hz.1, hz.2, hb.1, hb.2]

/-- **Enclosure with the rational margin `(3/5) E / 2^P`.** -/
theorem rs5_Z_enclosure_E' {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (ht4 : 4250 ≤ t) (hm : MarginOK c E) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 3 / 5 * ((E : ℝ) / 2 ^ c.P) ≤
        (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤
        (z.zhi : ℝ) / 2 ^ (2 * c.P) + 3 / 5 * ((E : ℝ) / 2 ^ c.P) := by
  obtain ⟨M, φ, hM, hpol, hφ, h1, h2⟩ := rs5_Z_enclosure' hv z h ht4
  have hmr := tpow_le_margin hv (by linarith) hm
  exact ⟨M, φ, hM, hpol, hφ, by linarith, by linarith⟩

theorem posOK'_real {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) {z : Cert} {E : ℕ}
    (hp : PosOK' c z E) : 3 / 5 * ((E : ℝ) / 2 ^ c.P) < (z.zlo : ℝ) / 2 ^ (2 * c.P) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((3 * (E : ℤ) * (c.one : ℤ) : ℤ) : ℝ) < ((5 * z.zlo : ℤ) : ℝ) := by exact_mod_cast hp
  push_cast at h
  rw [RS4.oneR hv] at h
  have e : (z.zlo : ℝ) / 2 ^ (2 * c.P) - 3 / 5 * ((E : ℝ) / 2 ^ c.P)
      = (5 * z.zlo - 3 * E * 2 ^ c.P) / (5 * (2 ^ c.P) ^ 2) := by
    rw [pow_mul']; field_simp
  have : 0 < (5 * (z.zlo : ℝ) - 3 * E * 2 ^ c.P) / (5 * (2 ^ c.P) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

theorem negOK'_real {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) {z : Cert} {E : ℕ}
    (hn : NegOK' c z E) : (z.zhi : ℝ) / 2 ^ (2 * c.P) < -(3 / 5 * ((E : ℝ) / 2 ^ c.P)) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((5 * z.zhi : ℤ) : ℝ) < ((-(3 * (E : ℤ) * (c.one : ℤ)) : ℤ) : ℝ) := by exact_mod_cast hn
  push_cast at h
  rw [RS4.oneR hv] at h
  have e : -(3 / 5 * ((E : ℝ) / 2 ^ c.P)) - (z.zhi : ℝ) / 2 ^ (2 * c.P)
      = (-(3 * E * 2 ^ c.P) - 5 * z.zhi) / (5 * (2 ^ c.P) ^ 2) := by
    rw [pow_mul']; field_simp
  have : 0 < (-(3 * (E : ℝ) * 2 ^ c.P) - 5 * z.zhi) / (5 * (2 ^ c.P) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

/-- A certified box above `(3/5) E / 2^P` (t >= 4250) gives `Re completedRiemannZeta(1/2+it) > 0`. -/
theorem rs5_sign_pos' {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (ht4 : 4250 ≤ t) (hm : MarginOK c E) (hpos : PosOK' c z E) :
    0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re := by
  obtain ⟨M, _, hM, _, _, h1, _⟩ := rs5_Z_enclosure_E' hv z h ht4 hm
  have := posOK'_real hv hpos
  have : 0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M := by linarith
  exact (div_pos_iff_of_pos_right hM).mp this

/-- A certified box below `-(3/5) E / 2^P` (t >= 4250) gives `Re completedRiemannZeta(1/2+it) < 0`. -/
theorem rs5_sign_neg' {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (ht4 : 4250 ≤ t) (hm : MarginOK c E) (hneg : NegOK' c z E) :
    (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re < 0 := by
  obtain ⟨M, _, hM, _, _, _, h2⟩ := rs5_Z_enclosure_E' hv z h ht4 hm
  have := negOK'_real hv hneg
  have : (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M < 0 := by linarith
  by_contra hc
  have := div_nonneg (not_lt.mp hc) hM.le
  linarith

/-- The decided height test is the real hypothesis `4250 <= s.t`. -/
theorem heightOK_real {s : Sample} (h : HeightOK s) : (4250 : ℝ) ≤ s.t := by
  unfold HeightOK at h
  unfold Sample.t
  have h' : ((4250 * 2 ^ s.tq : ℕ) : ℝ) ≤ ((s.tn : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  rw [le_div_iff₀ (by positivity)]
  exact h'

/-- **A sample accepted by `sampleOK'` has the claimed sign of `gLine`.** -/
theorem sampleOK'_sign {s : Sample} (h : sampleOK' s = true) :
    (s.pos = true → 0 < XiLineZeros.gLine s.t) ∧ (s.pos = false → XiLineZeros.gLine s.t < 0) := by
  unfold sampleOK' at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hH, hc⟩, hm⟩, hs⟩ := h
  have ht4 := heightOK_real hH
  constructor
  · intro hp
    rw [hp, if_pos rfl, decide_eq_true_eq] at hs
    exact rs5_sign_pos' s.valid s.z hc ht4 hm hs
  · intro hp
    rw [hp] at hs
    simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hs
    exact rs5_sign_neg' s.valid s.z hc ht4 hm hs

end

end RS5
