/-  EMZetaHighEval.lean -- the order-(2K+1) Euler-Maclaurin enclosure of ζ on the critical line,
    wired to the Nat-only kernel evaluator of the ArbEconomics seat (lane emhigh).

    Chain (all proved here, no numeric hypotheses):
      * `emFinite_line_split` : `emFinite K (1/2+it) N = psum t (N-1) + N^(-s) · emCorr K s N`;
      * `emCorr_line_re_im`   : `Re/Im emCorr K s N = emCorrRe/emCorrIm K (1/2) t N`
                                (closed real forms, `EMZetaHigh.emCorr_re_im`);
      * `zeta_ballK`          : two evaluator invariants (after `N-1` and `N` terms, from
                                `ArbEcon.chunk_sound`) plus ANY remainder bound `E` of the
                                order-(2K+1) finite part give explicit balls for Re ζ and Im ζ;
      * `zetaK_re_bounds` / `zetaK_im_bounds` : final forms `lo ≤ Re/Im ζ(1/2+it) ≤ hi` from rational
                                side conditions (checked per instance by `norm_num`).
    The remainder `E` comes from `EMZetaHigh.em_line_remainder_le` (general K, proved).

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/
import EMZetaHigh
import Probes.ArbEconomics_Zeta

open Complex ZetaReflection ZetaReflection.EMHigh

namespace ArbEcon

namespace OrderK

theorem sOf_eq (t : ℝ) : sOf t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  simp only [sOf]; push_cast; ring

/-- The Dirichlet split of the order-(2K+1) finite part on the critical line. -/
theorem emFinite_line_split (K : ℕ) (t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    emFinite K (sOf t) N = psum t (N - 1) + (N : ℂ) ^ (-sOf t) * emCorr K (sOf t) N := by
  simp only [emFinite, psum]
  rw [show N - 1 + 1 = N by omega]
  rfl

theorem emCorr_line_re_im (K : ℕ) (t : ℝ) (N : ℕ) :
    (emCorr K (sOf t) N).re = emCorrRe K (1 / 2) t N ∧
    (emCorr K (sOf t) N).im = emCorrIm K (1 / 2) t N := by
  rw [sOf_eq]; exact emCorr_re_im K (1 / 2) t N

/-- **The ball.**  Invariants after `N-1` and `N` terms, a remainder bound `E` for the order-(2K+1)
    finite part, and the real/imaginary parts `Bre, Bim` of the correction factor give
    `|Re ζ(s) 2^P - Cre| <= Rre`, `|Im ζ(s) 2^P - Cim| <= Rim`. -/
theorem zeta_ballK (c : Cfg) (K : ℕ) (t : ℝ) (N : ℕ) (hN : 2 ≤ N) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (E : ℝ)
    (hE : ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖ ≤ E) (Bre Bim : ℝ)
    (hBre : emCorrRe K (1 / 2) t N = Bre) (hBim : emCorrIm K (1 / 2) t N = Bim) :
    let a1 := (s1.reP : ℝ) - s1.reN
    let b1 := (s1.imP : ℝ) - s1.imN
    let za := ((s2.reP : ℝ) - s2.reN) - a1
    let zb := ((s2.imP : ℝ) - s2.imN) - b1
    let zra := (s2.reR : ℝ) + s1.reR
    let zrb := (s2.imR : ℝ) + s1.imR
    |(riemannZeta (sOf t)).re * 2 ^ c.P - (a1 + za * Bre - zb * Bim)|
        ≤ s1.reR + zra * |Bre| + zrb * |Bim| + E * 2 ^ c.P ∧
    |(riemannZeta (sOf t)).im * 2 ^ c.P - (b1 + za * Bim + zb * Bre)|
        ≤ s1.imR + zra * |Bim| + zrb * |Bre| + E * 2 ^ c.P := by
  intro a1 b1 za zb zra zrb
  obtain ⟨_, _, _, _, hre1, him1⟩ := h1
  obtain ⟨_, _, _, _, hre2, him2⟩ := h2
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have hNm : N - 1 + 1 = N := by omega
  have hZ : (N : ℂ) ^ (-sOf t) = psum t N - psum t (N - 1) := by
    have := psum_succ t (N - 1); rw [hNm] at this; rw [this]; ring
  have hZre : |((N : ℂ) ^ (-sOf t)).re * 2 ^ c.P - za| ≤ zra := by
    rw [hZ, Complex.sub_re]
    have : ((psum t N).re - (psum t (N - 1)).re) * 2 ^ c.P - za
        = ((psum t N).re * 2 ^ c.P - ((s2.reP : ℝ) - s2.reN))
          - ((psum t (N - 1)).re * 2 ^ c.P - a1) := by ring
    rw [this]; exact le_trans (abs_sub _ _) (add_le_add hre2 hre1)
  have hZim : |((N : ℂ) ^ (-sOf t)).im * 2 ^ c.P - zb| ≤ zrb := by
    rw [hZ, Complex.sub_im]
    have : ((psum t N).im - (psum t (N - 1)).im) * 2 ^ c.P - zb
        = ((psum t N).im * 2 ^ c.P - ((s2.imP : ℝ) - s2.imN))
          - ((psum t (N - 1)).im * 2 ^ c.P - b1) := by ring
    rw [this]; exact le_trans (abs_sub _ _) (add_le_add him2 him1)
  have hsplit := emFinite_line_split K t N (by omega)
  set B := emCorr K (sOf t) N with hB
  have hBre' : B.re = Bre := by rw [(emCorr_line_re_im K t N).1, hBre]
  have hBim' : B.im = Bim := by rw [(emCorr_line_re_im K t N).2, hBim]
  set Z := (N : ℂ) ^ (-sOf t)
  have hEre : |(riemannZeta (sOf t)).re - (emFinite K (sOf t) N).re| ≤ E := by
    rw [← Complex.sub_re]; exact le_trans (Complex.abs_re_le_norm _) hE
  have hEim : |(riemannZeta (sOf t)).im - (emFinite K (sOf t) N).im| ≤ E := by
    rw [← Complex.sub_im]; exact le_trans (Complex.abs_im_le_norm _) hE
  rw [hsplit] at hEre hEim
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, hBre', hBim']
    at hEre hEim
  constructor
  · have e : (riemannZeta (sOf t)).re * 2 ^ c.P - (a1 + za * Bre - zb * Bim)
        = ((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P
          + ((psum t (N - 1)).re * 2 ^ c.P - a1)
          + (Z.re * 2 ^ c.P - za) * Bre - (Z.im * 2 ^ c.P - zb) * Bim := by ring
    rw [e]
    have t1 : |((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim)))
        * 2 ^ c.P| ≤ E * 2 ^ c.P := by
      rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEre (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ c.P - za) * Bre| ≤ zra * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ c.P - zb) * Bim| ≤ zrb * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    have q1 := abs_add_le (((riemannZeta (sOf t)).re - ((psum t (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P + ((psum t (N - 1)).re * 2 ^ c.P - a1))
      ((Z.re * 2 ^ c.P - za) * Bre)
    have q2 := abs_add_le (((riemannZeta (sOf t)).re - ((psum t (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P) ((psum t (N - 1)).re * 2 ^ c.P - a1)
    have q3 := abs_sub (((riemannZeta (sOf t)).re - ((psum t (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P + ((psum t (N - 1)).re * 2 ^ c.P - a1)
      + (Z.re * 2 ^ c.P - za) * Bre) ((Z.im * 2 ^ c.P - zb) * Bim)
    linarith
  · have e : (riemannZeta (sOf t)).im * 2 ^ c.P - (b1 + za * Bim + zb * Bre)
        = ((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P
          + ((psum t (N - 1)).im * 2 ^ c.P - b1)
          + (Z.re * 2 ^ c.P - za) * Bim + (Z.im * 2 ^ c.P - zb) * Bre := by ring
    rw [e]
    have t1 : |((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre)))
        * 2 ^ c.P| ≤ E * 2 ^ c.P := by
      rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEim (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ c.P - za) * Bim| ≤ zra * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ c.P - zb) * Bre| ≤ zrb * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    have q1 := abs_add_le (((riemannZeta (sOf t)).im - ((psum t (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P + ((psum t (N - 1)).im * 2 ^ c.P - b1))
      ((Z.re * 2 ^ c.P - za) * Bim)
    have q2 := abs_add_le (((riemannZeta (sOf t)).im - ((psum t (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P) ((psum t (N - 1)).im * 2 ^ c.P - b1)
    have q3 := abs_add_le (((riemannZeta (sOf t)).im - ((psum t (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P + ((psum t (N - 1)).im * 2 ^ c.P - b1)
      + (Z.re * 2 ^ c.P - za) * Bim) ((Z.im * 2 ^ c.P - zb) * Bre)
    linarith

/-- **Final form (real part).**  With rational majorants `aRe ≥ |Bre|`, `aIm ≥ |Bim|`, two
    numeric side conditions turn the ball into `lo ≤ Re ζ(1/2 + i t) ≤ hi`. -/
theorem zetaK_re_bounds (c : Cfg) (K : ℕ) (t : ℝ) (N : ℕ) (hN : 2 ≤ N) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (E : ℝ)
    (hE : ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖ ≤ E) (Bre Bim : ℝ)
    (hBre : emCorrRe K (1 / 2) t N = Bre) (hBim : emCorrIm K (1 / 2) t N = Bim)
    (aRe aIm lo hi : ℝ) (haRe : |Bre| ≤ aRe) (haIm : |Bim| ≤ aIm)
    (hlo : lo * 2 ^ c.P ≤ (((s1.reP : ℝ) - s1.reN)
        + (((s2.reP : ℝ) - s2.reN) - ((s1.reP : ℝ) - s1.reN)) * Bre
        - (((s2.imP : ℝ) - s2.imN) - ((s1.imP : ℝ) - s1.imN)) * Bim)
      - ((s1.reR : ℝ) + ((s2.reR : ℝ) + s1.reR) * aRe + ((s2.imR : ℝ) + s1.imR) * aIm
          + E * 2 ^ c.P))
    (hhi : (((s1.reP : ℝ) - s1.reN)
        + (((s2.reP : ℝ) - s2.reN) - ((s1.reP : ℝ) - s1.reN)) * Bre
        - (((s2.imP : ℝ) - s2.imN) - ((s1.imP : ℝ) - s1.imN)) * Bim)
      + ((s1.reR : ℝ) + ((s2.reR : ℝ) + s1.reR) * aRe + ((s2.imR : ℝ) + s1.imR) * aIm
          + E * 2 ^ c.P)
      ≤ hi * 2 ^ c.P) :
    lo ≤ (riemannZeta (sOf t)).re ∧ (riemannZeta (sOf t)).re ≤ hi := by
  have hb := (zeta_ballK c K t N hN s1 s2 h1 h2 E hE Bre Bim hBre hBim).1
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have r1 : ((s2.reR : ℝ) + s1.reR) * |Bre| ≤ ((s2.reR : ℝ) + s1.reR) * aRe :=
    mul_le_mul_of_nonneg_left haRe (by positivity)
  have r2 : ((s2.imR : ℝ) + s1.imR) * |Bim| ≤ ((s2.imR : ℝ) + s1.imR) * aIm :=
    mul_le_mul_of_nonneg_left haIm (by positivity)
  rw [abs_le] at hb
  constructor
  · have : lo * 2 ^ c.P ≤ (riemannZeta (sOf t)).re * 2 ^ c.P := by linarith [hb.1]
    exact le_of_mul_le_mul_right this hP
  · have : (riemannZeta (sOf t)).re * 2 ^ c.P ≤ hi * 2 ^ c.P := by linarith [hb.2]
    exact le_of_mul_le_mul_right this hP

/-- **Final form (imaginary part).** -/
theorem zetaK_im_bounds (c : Cfg) (K : ℕ) (t : ℝ) (N : ℕ) (hN : 2 ≤ N) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (E : ℝ)
    (hE : ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖ ≤ E) (Bre Bim : ℝ)
    (hBre : emCorrRe K (1 / 2) t N = Bre) (hBim : emCorrIm K (1 / 2) t N = Bim)
    (aRe aIm lo hi : ℝ) (haRe : |Bre| ≤ aRe) (haIm : |Bim| ≤ aIm)
    (hlo : lo * 2 ^ c.P ≤ (((s1.imP : ℝ) - s1.imN)
        + (((s2.reP : ℝ) - s2.reN) - ((s1.reP : ℝ) - s1.reN)) * Bim
        + (((s2.imP : ℝ) - s2.imN) - ((s1.imP : ℝ) - s1.imN)) * Bre)
      - ((s1.imR : ℝ) + ((s2.reR : ℝ) + s1.reR) * aIm + ((s2.imR : ℝ) + s1.imR) * aRe
          + E * 2 ^ c.P))
    (hhi : (((s1.imP : ℝ) - s1.imN)
        + (((s2.reP : ℝ) - s2.reN) - ((s1.reP : ℝ) - s1.reN)) * Bim
        + (((s2.imP : ℝ) - s2.imN) - ((s1.imP : ℝ) - s1.imN)) * Bre)
      + ((s1.imR : ℝ) + ((s2.reR : ℝ) + s1.reR) * aIm + ((s2.imR : ℝ) + s1.imR) * aRe
          + E * 2 ^ c.P)
      ≤ hi * 2 ^ c.P) :
    lo ≤ (riemannZeta (sOf t)).im ∧ (riemannZeta (sOf t)).im ≤ hi := by
  have hb := (zeta_ballK c K t N hN s1 s2 h1 h2 E hE Bre Bim hBre hBim).2
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have r1 : ((s2.reR : ℝ) + s1.reR) * |Bim| ≤ ((s2.reR : ℝ) + s1.reR) * aIm :=
    mul_le_mul_of_nonneg_left haIm (by positivity)
  have r2 : ((s2.imR : ℝ) + s1.imR) * |Bre| ≤ ((s2.imR : ℝ) + s1.imR) * aRe :=
    mul_le_mul_of_nonneg_left haRe (by positivity)
  rw [abs_le] at hb
  constructor
  · have : lo * 2 ^ c.P ≤ (riemannZeta (sOf t)).im * 2 ^ c.P := by linarith [hb.1]
    exact le_of_mul_le_mul_right this hP
  · have : (riemannZeta (sOf t)).im * 2 ^ c.P ≤ hi * 2 ^ c.P := by linarith [hb.2]
    exact le_of_mul_le_mul_right this hP

end OrderK

end ArbEcon
