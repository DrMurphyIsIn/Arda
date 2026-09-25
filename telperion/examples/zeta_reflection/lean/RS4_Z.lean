/-  RS4_Z.lean -- lane B4: the kernel checker `RS4.check` glued to `RSInt.rs_Z_C0`.

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `rs4_Z_enclosure` : if the kernel accepts `(c, z)` (configuration valid at height `t`), there
        are `M > 0` and `phi` with `Gammaℝ(1/2+it) = M e^{i phi}`, `|phi - thetaMain t| <= 1/t`, and
            z.zlo / 2^(2P) - 2/1000 <= Re completedRiemannZeta(1/2+it) / M <= z.zhi / 2^(2P) + 2/1000.
        (`Re Lambda / M` is Hardy's Z(t), `M = |Gammaℝ(1/2+it)|`.)  The checker supplies every side
        condition of `rs_Z_C0` (t >= 10000, 0 < p, cos 2 pi p ≠ 0); the remainder 2 t^(-3/4) is
        bounded by 2/1000 using t >= 10000.
      * `rs4_sign_pos` / `rs4_sign_neg` : a box clearing `+-2/1000` pins the SIGN of
        `Re completedRiemannZeta(1/2+it)`.

    conjecture1_proved = False.  Finite-height sign certification; nothing about RH.
-/
import RS4_Sound
import RS_Bridge

open Complex
open scoped Real

namespace RS4

noncomputable section

theorem tpow_le {t : ℝ} (ht : 10000 ≤ t) : t ^ (-(3 / 4 : ℝ)) ≤ 1 / 1000 := by
  calc t ^ (-(3 / 4 : ℝ)) ≤ (10000 : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) ht (by norm_num)
    _ = 1 / 1000 := by
        rw [show (10000 : ℝ) = 10 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        rw [show (4 : ℝ) * (-(3 / 4)) = -(3 : ℕ) by norm_num, Real.rpow_neg (by norm_num),
          Real.rpow_natCast]
        norm_num

/-- **The certified enclosure of Hardy's Z** from an accepted certificate. -/
theorem rs4_Z_enclosure {c : ArbEcon.Cfg} {t : ℝ} {K : ℕ} (hv : ArbEcon.Valid c t K) (z : Cert)
    (h : check c z = true) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 2 / 1000 ≤ (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤ (z.zhi : ℝ) / 2 ^ (2 * c.P) + 2 / 1000 := by
  obtain ⟨ht, _, hp, hcos, hZ⟩ := check_sound hv z h
  obtain ⟨M, φ, hM, hpol, hφ, hb⟩ := RSInt.rs_Z_C0 ht hp hcos
  refine ⟨M, φ, hM, hpol, hφ, ?_⟩
  have hz := hZ φ hφ
  unfold Zmain at hz
  have hr := tpow_le ht
  rw [abs_le] at hb
  constructor <;> linarith [hz.1, hz.2, hb.1, hb.2]

/-- A certified box above `2/1000` gives `Re completedRiemannZeta(1/2+it) > 0`. -/
theorem rs4_sign_pos {c : ArbEcon.Cfg} {t : ℝ} {K : ℕ} (hv : ArbEcon.Valid c t K) (z : Cert)
    (h : check c z = true) (hpos : 2 / 1000 < (z.zlo : ℝ) / 2 ^ (2 * c.P)) :
    0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re := by
  obtain ⟨M, _, hM, _, _, h1, _⟩ := rs4_Z_enclosure hv z h
  have : 0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M := by linarith
  exact (div_pos_iff_of_pos_right hM).mp this

/-- A certified box below `-2/1000` gives `Re completedRiemannZeta(1/2+it) < 0`. -/
theorem rs4_sign_neg {c : ArbEcon.Cfg} {t : ℝ} {K : ℕ} (hv : ArbEcon.Valid c t K) (z : Cert)
    (h : check c z = true) (hneg : (z.zhi : ℝ) / 2 ^ (2 * c.P) < -(2 / 1000)) :
    (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re < 0 := by
  obtain ⟨M, _, hM, _, _, _, h2⟩ := rs4_Z_enclosure hv z h
  have : (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M < 0 := by linarith
  by_contra hc
  have := div_nonneg (not_lt.mp hc) hM.le
  linarith

end

end RS4
