/-  H1000Point.lean -- the point record and the pieces of the on-line sign certificate (lane
    h1000-prep; consumed by `H1000Line`).

    `LinePt` (height `t = tn / 2^tq`, EM cut, evaluator states, remainder and phase hints, claimed
    sign) and the kernel-evaluable pieces of `ptCheck`: the Dirichlet chunks `dirOk`
    (`ArbEcon.chunk_sound`), the integer zeta ball `zcX, zrX, zcY, zrY` at scale `zW`
    (`zball_sound`, from `EMZetaHighEval.zeta_ballK`, `EMZetaHighCheck.corr_eq`, `remOdd_sound`), the
    shifted phase interval `thLo, thHi` and its `trig` (`trig_phase`, from `H1000Phase.phase_sound` and
    `ArbEcon.trig_sound`), the product ball `sCtr ± sRad` of `S · 2^64 · W` (`s_ball`), and the
    positive magnitude factor of `gLine` (`gLine_eq_mag_mul`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.
-/
import H1000Phase
import SignChain

open Real Filter Topology
open ArbEcon ArbEcon.OrderK

namespace H1000Line

noncomputable section

/-! ## E. The point record, the Dirichlet chunks and the integer zeta ball. -/

/-- A kernel-checked on-line point: height `t = tn / 2^tq`, EM cut `N` (order 13, `K = 6`), the
    evaluator states `s1` (after `N - 1` terms) and `s2` (after `N`), the odd-saw remainder
    certificate `Q, r`, the phase hints `k` (`2^k ≤ A < 2^(k+1)`), `nl` (log series length), `m`
    (the `2π m` shift making the phase nonnegative), and the CLAIMED sign `pos` of `gLine t`. -/
structure LinePt where
  tn : ℕ
  tq : ℕ
  N : ℕ
  s1 : St
  s2 : St
  Q : ℕ
  r : ℕ
  k : ℕ
  nl : ℕ
  m : ℕ
  pos : Bool

/-- The height of a point. -/
def tOf (p : LinePt) : ℝ := (p.tn : ℝ) / 2 ^ p.tq

/-- The Dirichlet chunks: `s1` is the evaluator state after `N - 1` terms, `s2` after `N`. -/
def dirOk (p : LinePt) : Bool :=
  decide (2 ≤ p.N) && St.beq (run (cfg64 p.tn p.tq) (p.N - 2) (St.init (cfg64 p.tn p.tq))) p.s1 &&
    St.beq (run (cfg64 p.tn p.tq) 1 p.s1) p.s2

theorem dirOk_sound (p : LinePt) (h : dirOk p = true) :
    2 ≤ p.N ∧ Inv (cfg64 p.tn p.tq) (tOf p) (p.N - 1) p.s1 ∧
      Inv (cfg64 p.tn p.tq) (tOf p) p.N p.s2 := by
  simp only [dirOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hN, h1⟩, h2⟩ := h
  have hv := valid64 p.tn p.tq (tOf p) rfl
  have i0 := inv_init (cfg64 p.tn p.tq) (tOf p) hv.one_eq
  have i1 := chunk_sound _ _ 9 hv (p.N - 2) 1 _ _ i0 h1
  rw [show 1 + (p.N - 2) = p.N - 1 by omega] at i1
  have i2 := chunk_sound _ _ 9 hv 1 (p.N - 1) _ _ i1 h2
  rw [show p.N - 1 + 1 = p.N by omega] at i2
  exact ⟨hN, i1, i2⟩

/-- The remainder certificate `(ok, EN, ED)` of the point (order 13, odd saw). -/
def remP (p : LinePt) : Bool × ℤ × ℤ := remOdd 6 (2 ^ p.tq) p.tn p.N p.Q p.r

/-- The exact correction factor `(BreN, BimN, BD)` of the point. -/
def corP (p : LinePt) : ℤ × ℤ × ℤ := corrData 6 (2 ^ p.tq) p.tn p.N

/-- `W = 2^64 · BD · ED`, the common scale of the zeta ball. -/
def zW (p : LinePt) : ℤ := 2 ^ 64 * (corP p).2.2 * (remP p).2.2

/-- Centre of the `Re ζ` ball at scale `W` (the `checkCore` numerator `CreN`, times `ED`). -/
def zcX (p : LinePt) : ℤ :=
  (remP p).2.2 * ((((p.s1.reP : ℤ) - p.s1.reN)) * (corP p).2.2
    + (((p.s2.reP : ℤ) - p.s2.reN) - ((p.s1.reP : ℤ) - p.s1.reN)) * (corP p).1
    - (((p.s2.imP : ℤ) - p.s2.imN) - ((p.s1.imP : ℤ) - p.s1.imN)) * (corP p).2.1)

/-- Radius of the `Re ζ` ball at scale `W`. -/
def zrX (p : LinePt) : ℤ :=
  (remP p).2.2 * ((p.s1.reR : ℤ) * (corP p).2.2 + ((p.s2.reR : ℤ) + p.s1.reR) * ((corP p).1.natAbs : ℤ)
    + ((p.s2.imR : ℤ) + p.s1.imR) * ((corP p).2.1.natAbs : ℤ))
    + (corP p).2.2 * (remP p).2.1 * 2 ^ 64

/-- Centre of the `Im ζ` ball at scale `W`. -/
def zcY (p : LinePt) : ℤ :=
  (remP p).2.2 * ((((p.s1.imP : ℤ) - p.s1.imN)) * (corP p).2.2
    + (((p.s2.reP : ℤ) - p.s2.reN) - ((p.s1.reP : ℤ) - p.s1.reN)) * (corP p).2.1
    + (((p.s2.imP : ℤ) - p.s2.imN) - ((p.s1.imP : ℤ) - p.s1.imN)) * (corP p).1)

/-- Radius of the `Im ζ` ball at scale `W`. -/
def zrY (p : LinePt) : ℤ :=
  (remP p).2.2 * ((p.s1.imR : ℤ) * (corP p).2.2 + ((p.s2.reR : ℤ) + p.s1.reR) * ((corP p).2.1.natAbs : ℤ)
    + ((p.s2.imR : ℤ) + p.s1.imR) * ((corP p).1.natAbs : ℤ))
    + (corP p).2.2 * (remP p).2.1 * 2 ^ 64

/-- Scaling a ball by a positive factor. -/
theorem ball_scale {v c r K : ℝ} (hK : 0 < K) (h : |v - c| ≤ r) : |v * K - c * K| ≤ r * K := by
  rw [← sub_mul, abs_mul, abs_of_pos hK]
  exact mul_le_mul_of_nonneg_right h hK.le

/-- **The integer zeta ball.**  From the evaluator invariants after `N - 1` and `N` terms and the
    remainder certificate: `W > 0`, `|Re ζ(1/2+it) W - zcX| ≤ zrX`, `|Im ζ(1/2+it) W - zcY| ≤ zrY`. -/
theorem zball_sound (p : LinePt) (hN : 2 ≤ p.N)
    (h1 : Inv (cfg64 p.tn p.tq) (tOf p) (p.N - 1) p.s1) (h2 : Inv (cfg64 p.tn p.tq) (tOf p) p.N p.s2)
    (hR : (remP p).1 = true) (hED : 0 < (remP p).2.2) :
    (0 : ℝ) < (zW p : ℝ) ∧
    |(riemannZeta (sOf (tOf p))).re * (zW p : ℝ) - (zcX p : ℝ)| ≤ (zrX p : ℝ) ∧
    |(riemannZeta (sOf (tOf p))).im * (zW p : ℝ) - (zcY p : ℝ)| ≤ (zrY p : ℝ) := by
  have hu : 0 < 2 ^ p.tq := Nat.two_pow_pos _
  have ht' : tOf p = (p.tn : ℝ) / ((2 ^ p.tq : ℕ) : ℝ) := by simp [tOf]
  obtain ⟨hcre, hcim⟩ := corr_eq 6 (2 ^ p.tq) p.tn p.N (by norm_num) (by norm_num) hu (by omega)
    (tOf p) ht'
  have hE := remOdd_sound 6 p.N (by norm_num) (by omega) (2 ^ p.tq) p.tn hu (tOf p) ht' p.Q p.r hR
  have hball := zeta_ballK (cfg64 p.tn p.tq) 6 (tOf p) p.N hN p.s1 p.s2 h1 h2 _ hE _ _ hcre hcim
  have hP : (cfg64 p.tn p.tq).P = 64 := rfl
  rw [hP] at hball
  obtain ⟨hre, him⟩ := hball
  -- names for the integer data
  have hremP : remOdd 6 (2 ^ p.tq) p.tn p.N p.Q p.r = remP p := rfl
  have hcorP : corrData 6 (2 ^ p.tq) p.tn p.N = corP p := rfl
  rw [hremP, hcorP] at hre him
  simp only [zW, zcX, zrX, zcY, zrY]
  set BreN := (corP p).1 with hBreN
  set BimN := (corP p).2.1 with hBimN
  set BD := (corP p).2.2 with hBD
  set EN := (remP p).2.1 with hEN
  set ED := (remP p).2.2 with hEDdef
  -- positivity of BD (as in `checkCore_sound`)
  have hBDpos : (0 : ℝ) < (BD : ℝ) := by
    have e : (BD : ℝ) = 2 * (((2 ^ p.tq : ℕ) : ℝ) * (2 ^ p.tq : ℕ) + (2 * p.tn) * (2 * p.tn))
        * ((Lbeta : ℝ) * (2 * (2 ^ p.tq : ℕ) * p.N) ^ (2 * 6 - 1)) := by
      simp only [hBD, corP, corrData]; push_cast; ring
    rw [e]
    have hL : (0 : ℝ) < (Lbeta : ℝ) := by norm_num [Lbeta]
    have hNR : (0 : ℝ) < p.N := by exact_mod_cast (show 0 < p.N by omega)
    positivity
  have hEDR : (0 : ℝ) < (ED : ℝ) := by exact_mod_cast hED
  have hK : (0 : ℝ) < (BD : ℝ) * ED := mul_pos hBDpos hEDR
  have hWpos : (0 : ℝ) < ((2 ^ 64 * BD * ED : ℤ) : ℝ) := by push_cast; positivity
  refine ⟨hWpos, ?_, ?_⟩
  · have hs := ball_scale hK hre
    have hnat1 : ((BreN.natAbs : ℤ) : ℝ) = |(BreN : ℝ)| := by
      rw [Int.natCast_natAbs, Int.cast_abs]
    have hnat2 : ((BimN.natAbs : ℤ) : ℝ) = |(BimN : ℝ)| := by
      rw [Int.natCast_natAbs, Int.cast_abs]
    push_cast [hnat1, hnat2]
    rw [abs_div, abs_div, abs_of_pos hBDpos] at hs
    have e1 : (riemannZeta (sOf (tOf p))).re * 2 ^ 64 * ((BD : ℝ) * ED)
        = (riemannZeta (sOf (tOf p))).re * (2 ^ 64 * (BD : ℝ) * ED) := by ring
    rw [e1] at hs
    convert hs using 2
    · field_simp
      ring
    · field_simp
      ring
  · have hs := ball_scale hK him
    have hnat1 : ((BreN.natAbs : ℤ) : ℝ) = |(BreN : ℝ)| := by
      rw [Int.natCast_natAbs, Int.cast_abs]
    have hnat2 : ((BimN.natAbs : ℤ) : ℝ) = |(BimN : ℝ)| := by
      rw [Int.natCast_natAbs, Int.cast_abs]
    push_cast [hnat1, hnat2]
    rw [abs_div, abs_div, abs_of_pos hBDpos] at hs
    have e1 : (riemannZeta (sOf (tOf p))).im * 2 ^ 64 * ((BD : ℝ) * ED)
        = (riemannZeta (sOf (tOf p))).im * (2 ^ 64 * (BD : ℝ) * ED) := by ring
    rw [e1] at hs
    convert hs using 2
    · field_simp
      ring
    · field_simp
      ring

/-! ## F. The product ball and the sign test. -/

/-- `|αβ - Cc| ≤ r1 (|c| + r2) + |C| r2` from `|α - C| ≤ r1`, `|β - c| ≤ r2`. -/
theorem prod_ball {α β C c r1 r2 : ℝ} (h1 : |α - C| ≤ r1) (h2 : |β - c| ≤ r2) :
    |α * β - C * c| ≤ r1 * (|c| + r2) + |C| * r2 := by
  have e : α * β - C * c = (α - C) * β + C * (β - c) := by ring
  rw [e]
  have hb : |β| ≤ |c| + r2 := by
    have := abs_sub_abs_le_abs_sub β c
    linarith
  have hr1 : 0 ≤ r1 := le_trans (abs_nonneg _) h1
  calc |(α - C) * β + C * (β - c)| ≤ |(α - C) * β| + |C * (β - c)| := abs_add_le _ _
    _ = |α - C| * |β| + |C| * |β - c| := by rw [abs_mul, abs_mul]
    _ ≤ r1 * (|c| + r2) + |C| * r2 :=
        add_le_add (mul_le_mul h1 hb (abs_nonneg _) hr1) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))

/-- Integer sign `±1` of a Bool (`true` = `+1`), the integer form of `ArbEcon.sgn`. -/
def sgnI (b : Bool) : ℤ := Bool.rec (-1) 1 b

theorem sgnI_cast (b : Bool) : ((sgnI b : ℤ) : ℝ) = sgn b := by
  cases b <;> simp [sgnI, sgn]

/-- The shifted phase interval (scale `2^64`) fed to `trig`: lower end. -/
def thLo (p : LinePt) : ℤ := phaseLo p.tn p.tq p.k p.nl + (p.m : ℤ) * (TPLO : ℤ)

/-- The shifted phase interval: upper end. -/
def thHi (p : LinePt) : ℤ := phaseHi p.tn p.tq p.k p.nl + (p.m : ℤ) * (TPHI : ℤ)

/-- cos / sin of the (shifted) phase, by the evaluator's `trig`. -/
def trigP (p : LinePt) : Trig := trig (cfg64 p.tn p.tq) (thLo p).toNat (thHi p).toNat

/-- Centre of `S · 2^64 · W` (`S = cos φ Re ζ - sin φ Im ζ`). -/
def sCtr (p : LinePt) : ℤ :=
  sgnI (trigP p).cs * ((trigP p).cm : ℤ) * zcX p - sgnI (trigP p).ss * ((trigP p).sm : ℤ) * zcY p

/-- Radius of `S · 2^64 · W`. -/
def sRad (p : LinePt) : ℤ :=
  ((trigP p).cr : ℤ) * (((zcX p).natAbs : ℤ) + zrX p) + ((trigP p).cm : ℤ) * zrX p
    + ((trigP p).sr : ℤ) * (((zcY p).natAbs : ℤ) + zrY p) + ((trigP p).sm : ℤ) * zrY p

/-- **The point checker.**  Dirichlet chunks, remainder certificate, phase side conditions, and the
    claimed sign of `S` (hence of `gLine t`) certified by the product ball. -/
def ptCheck (p : LinePt) : Bool :=
  dirOk p && (remP p).1 && decide (0 < (remP p).2.2) && phaseOk p.tn p.tq p.k &&
    decide (0 ≤ thLo p) &&
    (bif p.pos then decide (sRad p < sCtr p) else decide (sCtr p + sRad p < 0))

/-- The phase of the point, `φ = Λ - (t/2) log π`. -/
def phiOf (p : LinePt) (Λ : ℝ) : ℝ := Λ - tOf p / 2 * Real.log π

/-- **cos / sin of the phase.**  Under the phase side conditions, `trigP p` is a signed ball of
    `cos φ`, `sin φ` at scale `2^64` for the branch limit `Λ`. -/
theorem trig_phase (p : LinePt) (hph : phaseOk p.tn p.tq p.k = true) (hlo0 : 0 ≤ thLo p) (Λ : ℝ)
    (hΛ : Tendsto (ThetaGap.imLnVal (1 / 4) (tOf p / 2)) atTop (𝓝 Λ)) :
    |Real.cos (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).cs * ((trigP p).cm : ℝ)| ≤ ((trigP p).cr : ℝ) ∧
    |Real.sin (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).ss * ((trigP p).sm : ℝ)| ≤ ((trigP p).sr : ℝ) := by
  obtain ⟨ph1, ph2⟩ := phase_sound p.tn p.tq p.k p.nl hph Λ hΛ
  have ph1' : ((phaseLo p.tn p.tq p.k p.nl : ℤ) : ℝ) ≤ phiOf p Λ * 2 ^ 64 := ph1
  have ph2' : phiOf p Λ * 2 ^ 64 ≤ ((phaseHi p.tn p.tq p.k p.nl : ℤ) : ℝ) := ph2
  obtain ⟨tp1, tp2⟩ := twopi_scaled
  have hm0 : (0 : ℝ) ≤ p.m := by positivity
  have m1 := mul_le_mul_of_nonneg_left tp1 hm0
  have m2 := mul_le_mul_of_nonneg_left tp2 hm0
  have e2 : (phiOf p Λ + (p.m : ℝ) * (2 * π)) * 2 ^ 64
      = phiOf p Λ * 2 ^ 64 + (p.m : ℝ) * (2 * π * 2 ^ 64) := by ring
  have hlo : (((thLo p).toNat : ℕ) : ℝ) ≤ (phiOf p Λ + (p.m : ℝ) * (2 * π)) * 2 ^ 64 := by
    have e : (((thLo p).toNat : ℕ) : ℝ) = ((thLo p : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hlo0]
    rw [e, e2]
    simp only [thLo, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linarith
  have hhi : (phiOf p Λ + (p.m : ℝ) * (2 * π)) * 2 ^ 64 ≤ (((thHi p).toNat : ℕ) : ℝ) := by
    have e : ((thHi p : ℤ) : ℝ) ≤ (((thHi p).toNat : ℕ) : ℝ) := by
      rw [← Int.cast_natCast]; exact_mod_cast Int.self_le_toNat (thHi p)
    refine le_trans ?_ e
    rw [e2]
    simp only [thHi, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linarith
  have htr := trig_sound (cfg64 p.tn p.tq) (tOf p) 9 (valid64 p.tn p.tq (tOf p) rfl)
    (phiOf p Λ + (p.m : ℝ) * (2 * π)) _ _ hlo hhi
  obtain ⟨hc, hsn, _, _⟩ := htr
  unfold SBall at hc hsn
  rw [Real.cos_add_nat_mul_two_pi] at hc
  rw [Real.sin_add_nat_mul_two_pi] at hsn
  exact ⟨hc, hsn⟩

/-- **The ball of `S · 2^64 · W`**, `S = cos φ Re ζ - sin φ Im ζ`, around `sCtr` of radius `sRad`. -/
theorem s_ball (p : LinePt) (Λ : ℝ)
    (hc : |Real.cos (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).cs * ((trigP p).cm : ℝ)| ≤ ((trigP p).cr : ℝ))
    (hsn : |Real.sin (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).ss * ((trigP p).sm : ℝ)| ≤ ((trigP p).sr : ℝ))
    (hX : |(riemannZeta (sOf (tOf p))).re * (zW p : ℝ) - (zcX p : ℝ)| ≤ (zrX p : ℝ))
    (hY : |(riemannZeta (sOf (tOf p))).im * (zW p : ℝ) - (zcY p : ℝ)| ≤ (zrY p : ℝ)) :
    |(Real.cos (phiOf p Λ) * (riemannZeta (sOf (tOf p))).re
        - Real.sin (phiOf p Λ) * (riemannZeta (sOf (tOf p))).im) * 2 ^ 64 * (zW p : ℝ)
      - (sCtr p : ℝ)| ≤ (sRad p : ℝ) := by
  have pc := prod_ball hc hX
  have ps := prod_ball hsn hY
  have habsC : |sgn (trigP p).cs * ((trigP p).cm : ℝ)| = ((trigP p).cm : ℝ) := by
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (by positivity)]
  have habsS : |sgn (trigP p).ss * ((trigP p).sm : ℝ)| = ((trigP p).sm : ℝ) := by
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (by positivity)]
  rw [habsC] at pc
  rw [habsS] at ps
  have hctr : ((sCtr p : ℤ) : ℝ) = sgn (trigP p).cs * ((trigP p).cm : ℝ) * (zcX p : ℝ)
      - sgn (trigP p).ss * ((trigP p).sm : ℝ) * (zcY p : ℝ) := by
    simp only [sCtr, Int.cast_sub, Int.cast_mul, Int.cast_natCast, sgnI_cast]
  have hrad : ((sRad p : ℤ) : ℝ) = ((trigP p).cr : ℝ) * (|(zcX p : ℝ)| + (zrX p : ℝ))
      + ((trigP p).cm : ℝ) * (zrX p : ℝ) + ((trigP p).sr : ℝ) * (|(zcY p : ℝ)| + (zrY p : ℝ))
      + ((trigP p).sm : ℝ) * (zrY p : ℝ) := by
    simp only [sRad, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hctr, hrad]
  set X := (riemannZeta (sOf (tOf p))).re
  set Y := (riemannZeta (sOf (tOf p))).im
  have e : (Real.cos (phiOf p Λ) * X - Real.sin (phiOf p Λ) * Y) * 2 ^ 64 * (zW p : ℝ)
      - (sgn (trigP p).cs * ((trigP p).cm : ℝ) * (zcX p : ℝ)
        - sgn (trigP p).ss * ((trigP p).sm : ℝ) * (zcY p : ℝ))
      = (Real.cos (phiOf p Λ) * 2 ^ 64 * (X * (zW p : ℝ))
          - sgn (trigP p).cs * ((trigP p).cm : ℝ) * (zcX p : ℝ))
        - (Real.sin (phiOf p Λ) * 2 ^ 64 * (Y * (zW p : ℝ))
          - sgn (trigP p).ss * ((trigP p).sm : ℝ) * (zcY p : ℝ)) := by ring
  rw [e]
  refine le_trans (abs_sub _ _) ?_
  linarith [pc, ps]

/-- The sign of `gLine t` is the sign of `S = cos φ Re ζ - sin φ Im ζ` (`M(t) > 0`). -/
theorem gLine_eq_mag_mul (p : LinePt) (htpos : 0 < tOf p) :
    ∃ Λ : ℝ, Tendsto (ThetaGap.imLnVal (1 / 4) (tOf p / 2)) atTop (𝓝 Λ) ∧
      0 < KernelGammaEnvelope.gammaRMag (tOf p) ∧
      XiLineZeros.gLine (tOf p) = KernelGammaEnvelope.gammaRMag (tOf p)
        * (Real.cos (phiOf p Λ) * (riemannZeta (sOf (tOf p))).re
          - Real.sin (phiOf p Λ) * (riemannZeta (sOf (tOf p))).im) := by
  obtain ⟨Λ, hΛ, hdec⟩ := KernelGammaEnvelope.gLine_decomp_explicit (tOf p) (ne_of_gt htpos)
  have hMpos : 0 < KernelGammaEnvelope.gammaRMag (tOf p) :=
    lt_of_lt_of_le (by positivity) (KernelGammaEnvelope.gammaRMag_bounds (tOf p)).1
  exact ⟨Λ, hΛ, hMpos, hdec⟩

end

end H1000Line
