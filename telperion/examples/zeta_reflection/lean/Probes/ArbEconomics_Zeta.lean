/-  Probes/ArbEconomics_Zeta.lean -- from the evaluator invariant to kernel-checked enclosures of
    Re / Im zeta(1/2 + i t).

    Chain (all proved here, no numeric hypotheses):
      * `emZetaFinite3_split` : `emZetaFinite3 s N = psum t (N-1) + N^(-s) * B(t, N)` with
        `B = N/(s-1) + 1/2 + s/(12 N)` (from `ZetaEMSum.emZetaFinite3_eq_dirichlet`);
      * `B_re`, `B_im`       : closed real forms of `B`;
      * `em3_remainder_le`   : the island's order-3 Euler-Maclaurin remainder
        (`EMZetaTail.em_zeta_critical_line3_enclosure`) bounded by `Q / (180 N^2 r)` for rational
        `Q >= |s(s+1)(s+2)|` and `r <= sqrt N`;
      * `zeta_ball`          : two evaluator invariants (after `N-1` and `N` terms) plus the
        remainder bound give explicit balls for `Re zeta` and `Im zeta`.
    An instance then needs only kernel-checked chunks and one `norm_num` on rationals.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/
import Probes.ArbEconomics_Sound
import ZetaEMSum

open Complex ZetaReflection

namespace ArbEcon

/-- `s = 1/2 + i t` -/
noncomputable def sOf (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

theorem sOf_re (t : ℝ) : (sOf t).re = 1 / 2 := by simp [sOf]
theorem sOf_im (t : ℝ) : (sOf t).im = t := by simp [sOf]

theorem psum_succ (t : ℝ) (n : ℕ) :
    psum t (n + 1) = psum t n + ((n + 1 : ℕ) : ℂ) ^ (-sOf t) := by
  simp only [psum]
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
  rfl

/-- The Dirichlet split of the EM finite part. -/
theorem emZetaFinite3_split (t : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    emZetaFinite3 (sOf t) N
      = psum t (N - 1) + (N : ℂ) ^ (-sOf t) * ((N : ℂ) / (sOf t - 1) + 1 / 2 + sOf t / (12 * N)) := by
  have hs0 : sOf t ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [sOf_re] at this; simp at this
  have hs1 : sOf t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [sOf_re] at this; norm_num at this
  have hsre : -1 < (-sOf t).re := by rw [Complex.neg_re, sOf_re]; norm_num
  rw [ZetaEMSum.emZetaFinite3_eq_dirichlet hs0 hs1 (by omega) hsre]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hsum : (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-sOf t)) = psum t (N - 1) := by
    simp only [psum]
    rw [show N - 1 + 1 = N by omega]
    rfl
  have h1 : (N : ℂ) ^ (1 - sOf t) = N * (N : ℂ) ^ (-sOf t) := by
    rw [show (1 : ℂ) - sOf t = 1 + -sOf t by ring, Complex.cpow_add _ _ hN0, Complex.cpow_one]
  have h2 : ((N : ℝ) : ℂ) ^ (-sOf t - 1) = (N : ℂ) ^ (-sOf t) / N := by
    rw [Complex.ofReal_natCast, show -sOf t - 1 = -sOf t + -1 by ring, Complex.cpow_add _ _ hN0,
      Complex.cpow_neg_one, div_eq_mul_inv]
  have hsm1 : sOf t - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [hsum, h1, h2, bernoulli_two]
  field_simp
  ring

theorem B_re (t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℂ) / (sOf t - 1) + 1 / 2 + sOf t / (12 * N)).re
      = -(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  simp only [Complex.add_re, Complex.div_re, Complex.sub_re, Complex.sub_im, sOf_re, sOf_im,
    Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  field_simp
  ring

theorem B_im (t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℂ) / (sOf t - 1) + 1 / 2 + sOf t / (12 * N)).im
      = -(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  simp only [Complex.add_im, Complex.div_im, Complex.sub_re, Complex.sub_im, sOf_re, sOf_im,
    Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  field_simp
  ring

/-- The order-3 EM remainder in rational form. -/
theorem em3_remainder_le (t : ℝ) (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (hQ0 : 0 ≤ Q)
    (hQ : (1 / 4 + t ^ 2) * (9 / 4 + t ^ 2) * (25 / 4 + t ^ 2) ≤ Q ^ 2)
    (r : ℕ) (hr0 : 0 < r) (hr : r ^ 2 ≤ N) :
    ‖riemannZeta (sOf t) - emZetaFinite3 (sOf t) N‖ ≤ Q / (180 * N ^ 2 * r) := by
  have h := em_zeta_critical_line3_enclosure t hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  -- the norm of s(s+1)(s+2)
  have hnorm : ‖((1 / 2 : ℂ) + t * Complex.I) * ((1 / 2 : ℂ) + t * Complex.I + 1)
      * ((1 / 2 : ℂ) + t * Complex.I + 2)‖ ≤ Q := by
    rw [norm_mul, norm_mul]
    have e1 : ‖(1 / 2 : ℂ) + t * Complex.I‖ = Real.sqrt (1 / 4 + t ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
    have e2 : ‖(1 / 2 : ℂ) + t * Complex.I + 1‖ = Real.sqrt (9 / 4 + t ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
    have e3 : ‖(1 / 2 : ℂ) + t * Complex.I + 2‖ = Real.sqrt (25 / 4 + t ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
    rw [e1, e2, e3, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_le_left]
    · exact hQ
    · exact hQ0
  -- N^(-5/2) <= 1 / (N^2 r)
  have hpow : (N : ℝ) ^ (-((1 / 2 : ℝ) + 3 - 1)) ≤ 1 / ((N : ℝ) ^ 2 * r) := by
    have hsq : (r : ℝ) ≤ Real.sqrt N := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast hr
    have e : (N : ℝ) ^ (-((1 / 2 : ℝ) + 3 - 1)) = 1 / ((N : ℝ) ^ 2 * Real.sqrt N) := by
      rw [show -((1 / 2 : ℝ) + 3 - 1) = -((2 : ℕ) + (1 / 2 : ℝ)) by norm_num,
        Real.rpow_neg (le_of_lt hNR), Real.rpow_add hNR, Real.rpow_natCast, ← Real.sqrt_eq_rpow,
        one_div]
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  refine le_trans h ?_
  have e2 : ((1 / 2 : ℝ) + 3 - 1) = 5 / 2 := by norm_num
  rw [e2]
  rw [e2] at hpow
  have hNr : (0 : ℝ) < (N : ℝ) ^ 2 * r := by positivity
  calc (1 / 12) * ‖((1 / 2 : ℂ) + t * Complex.I) * ((1 / 2 : ℂ) + t * Complex.I + 1)
          * ((1 / 2 : ℂ) + t * Complex.I + 2)‖ * (N : ℝ) ^ (-(5 / 2 : ℝ)) / (5 / 2) / 6
      ≤ (1 / 12) * Q * (1 / ((N : ℝ) ^ 2 * r)) / (5 / 2) / 6 := by
        gcongr
    _ = Q / (180 * N ^ 2 * r) := by field_simp; ring

/-- **The enclosure.**  Invariants after `N-1` and `N` terms and the remainder bound `E` give
    `|Re zeta(s) 2^P - Cre| <= Rre` and `|Im zeta(s) 2^P - Cim| <= Rim` with explicit
    `Cre, Rre, Cim, Rim` (the N-th term is the difference of the two partial sums). -/
theorem zeta_ball (c : Cfg) (t : ℝ) (N : ℕ) (hN : 2 ≤ N) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (E : ℝ)
    (hE : ‖riemannZeta (sOf t) - emZetaFinite3 (sOf t) N‖ ≤ E) :
    let Bre := -(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N)
    let Bim := -(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N)
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
  intro Bre Bim a1 b1 za zb zra zrb
  obtain ⟨_, _, _, _, hre1, him1⟩ := h1
  obtain ⟨_, _, _, _, hre2, him2⟩ := h2
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have hNm : N - 1 + 1 = N := by omega
  -- the N-th term Z = psum N - psum (N-1)
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
  have hsplit := emZetaFinite3_split t N hN
  set B := (N : ℂ) / (sOf t - 1) + 1 / 2 + sOf t / (12 * N) with hB
  have hBre : B.re = Bre := B_re t N (by omega)
  have hBim : B.im = Bim := B_im t N (by omega)
  set Z := (N : ℂ) ^ (-sOf t)
  have hEre : |(riemannZeta (sOf t)).re - (emZetaFinite3 (sOf t) N).re| ≤ E := by
    rw [← Complex.sub_re]; exact le_trans (Complex.abs_re_le_norm _) hE
  have hEim : |(riemannZeta (sOf t)).im - (emZetaFinite3 (sOf t) N).im| ≤ E := by
    rw [← Complex.sub_im]; exact le_trans (Complex.abs_im_le_norm _) hE
  rw [hsplit] at hEre hEim
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, hBre, hBim] at hEre hEim
  constructor
  · -- Re
    have e : (riemannZeta (sOf t)).re * 2 ^ c.P - (a1 + za * Bre - zb * Bim)
        = ((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P
          + ((psum t (N - 1)).re * 2 ^ c.P - a1)
          + (Z.re * 2 ^ c.P - za) * Bre - (Z.im * 2 ^ c.P - zb) * Bim := by ring
    rw [e]
    have t1 : |((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P|
        ≤ E * 2 ^ c.P := by rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEre (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ c.P - za) * Bre| ≤ zra * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ c.P - zb) * Bim| ≤ zrb * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    calc _ ≤ |((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P
              + ((psum t (N - 1)).re * 2 ^ c.P - a1) + (Z.re * 2 ^ c.P - za) * Bre|
            + |(Z.im * 2 ^ c.P - zb) * Bim| := abs_sub _ _
      _ ≤ (|((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P|
            + |(psum t (N - 1)).re * 2 ^ c.P - a1| + |(Z.re * 2 ^ c.P - za) * Bre|)
            + |(Z.im * 2 ^ c.P - zb) * Bim| := by
          have := abs_add_le (((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim)))
            * 2 ^ c.P + ((psum t (N - 1)).re * 2 ^ c.P - a1)) ((Z.re * 2 ^ c.P - za) * Bre)
          have := abs_add_le (((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim)))
            * 2 ^ c.P) ((psum t (N - 1)).re * 2 ^ c.P - a1)
          linarith
      _ ≤ s1.reR + zra * |Bre| + zrb * |Bim| + E * 2 ^ c.P := by linarith
  · -- Im
    have e : (riemannZeta (sOf t)).im * 2 ^ c.P - (b1 + za * Bim + zb * Bre)
        = ((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P
          + ((psum t (N - 1)).im * 2 ^ c.P - b1)
          + (Z.re * 2 ^ c.P - za) * Bim + (Z.im * 2 ^ c.P - zb) * Bre := by ring
    rw [e]
    have t1 : |((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P|
        ≤ E * 2 ^ c.P := by rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEim (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ c.P - za) * Bim| ≤ zra * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ c.P - zb) * Bre| ≤ zrb * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    calc _ ≤ |((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P
              + ((psum t (N - 1)).im * 2 ^ c.P - b1) + (Z.re * 2 ^ c.P - za) * Bim|
            + |(Z.im * 2 ^ c.P - zb) * Bre| := abs_add_le _ _
      _ ≤ (|((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P|
            + |(psum t (N - 1)).im * 2 ^ c.P - b1| + |(Z.re * 2 ^ c.P - za) * Bim|)
            + |(Z.im * 2 ^ c.P - zb) * Bre| := by
          have := abs_add_le (((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre)))
            * 2 ^ c.P + ((psum t (N - 1)).im * 2 ^ c.P - b1)) ((Z.re * 2 ^ c.P - za) * Bim)
          have := abs_add_le (((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre)))
            * 2 ^ c.P) ((psum t (N - 1)).im * 2 ^ c.P - b1)
          linarith
      _ ≤ s1.imR + zra * |Bim| + zrb * |Bre| + E * 2 ^ c.P := by linarith

/-- **Final form (real part).**  With rational majorants `aRe >= |Re B|`, `aIm >= |Im B|`, two
    numeric side conditions (checked per instance by `norm_num`) turn the ball into
    `lo ≤ Re zeta(1/2 + i t) ≤ hi`. -/
theorem zeta_re_bounds (c : Cfg) (t : ℝ) (N : ℕ) (hN : 2 ≤ N) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (E : ℝ)
    (hE : ‖riemannZeta (sOf t) - emZetaFinite3 (sOf t) N‖ ≤ E) (aRe aIm lo hi : ℝ)
    (haRe : |-(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N)| ≤ aRe)
    (haIm : |-(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N)| ≤ aIm)
    (hlo : lo * 2 ^ c.P ≤ (((s1.reP : ℝ) - s1.reN)
        + (((s2.reP : ℝ) - s2.reN) - ((s1.reP : ℝ) - s1.reN)) * (-(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N))
        - (((s2.imP : ℝ) - s2.imN) - ((s1.imP : ℝ) - s1.imN)) * (-(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N)))
      - ((s1.reR : ℝ) + ((s2.reR : ℝ) + s1.reR) * aRe + ((s2.imR : ℝ) + s1.imR) * aIm + E * 2 ^ c.P))
    (hhi : (((s1.reP : ℝ) - s1.reN)
        + (((s2.reP : ℝ) - s2.reN) - ((s1.reP : ℝ) - s1.reN)) * (-(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N))
        - (((s2.imP : ℝ) - s2.imN) - ((s1.imP : ℝ) - s1.imN)) * (-(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N)))
      + ((s1.reR : ℝ) + ((s2.reR : ℝ) + s1.reR) * aRe + ((s2.imR : ℝ) + s1.imR) * aIm + E * 2 ^ c.P)
      ≤ hi * 2 ^ c.P) :
    lo ≤ (riemannZeta (sOf t)).re ∧ (riemannZeta (sOf t)).re ≤ hi := by
  have hb := (zeta_ball c t N hN s1 s2 h1 h2 E hE).1
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have r1 : ((s2.reR : ℝ) + s1.reR) * |-(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N)|
      ≤ ((s2.reR : ℝ) + s1.reR) * aRe := mul_le_mul_of_nonneg_left haRe (by positivity)
  have r2 : ((s2.imR : ℝ) + s1.imR) * |-(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N)|
      ≤ ((s2.imR : ℝ) + s1.imR) * aIm := mul_le_mul_of_nonneg_left haIm (by positivity)
  rw [abs_le] at hb
  constructor
  · have : lo * 2 ^ c.P ≤ (riemannZeta (sOf t)).re * 2 ^ c.P := by linarith [hb.1]
    exact le_of_mul_le_mul_right this hP
  · have : (riemannZeta (sOf t)).re * 2 ^ c.P ≤ hi * 2 ^ c.P := by linarith [hb.2]
    exact le_of_mul_le_mul_right this hP

/-- **Final form (imaginary part).** -/
theorem zeta_im_bounds (c : Cfg) (t : ℝ) (N : ℕ) (hN : 2 ≤ N) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (E : ℝ)
    (hE : ‖riemannZeta (sOf t) - emZetaFinite3 (sOf t) N‖ ≤ E) (aRe aIm lo hi : ℝ)
    (haRe : |-(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N)| ≤ aRe)
    (haIm : |-(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N)| ≤ aIm)
    (hlo : lo * 2 ^ c.P ≤ (((s1.imP : ℝ) - s1.imN)
        + (((s2.reP : ℝ) - s2.reN) - ((s1.reP : ℝ) - s1.reN)) * (-(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N))
        + (((s2.imP : ℝ) - s2.imN) - ((s1.imP : ℝ) - s1.imN)) * (-(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N)))
      - ((s1.imR : ℝ) + ((s2.reR : ℝ) + s1.reR) * aIm + ((s2.imR : ℝ) + s1.imR) * aRe + E * 2 ^ c.P))
    (hhi : (((s1.imP : ℝ) - s1.imN)
        + (((s2.reP : ℝ) - s2.reN) - ((s1.reP : ℝ) - s1.reN)) * (-(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N))
        + (((s2.imP : ℝ) - s2.imN) - ((s1.imP : ℝ) - s1.imN)) * (-(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N)))
      + ((s1.imR : ℝ) + ((s2.reR : ℝ) + s1.reR) * aIm + ((s2.imR : ℝ) + s1.imR) * aRe + E * 2 ^ c.P)
      ≤ hi * 2 ^ c.P) :
    lo ≤ (riemannZeta (sOf t)).im ∧ (riemannZeta (sOf t)).im ≤ hi := by
  have hb := (zeta_ball c t N hN s1 s2 h1 h2 E hE).2
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have r1 : ((s2.reR : ℝ) + s1.reR) * |-(N : ℝ) * t / (1 / 4 + t ^ 2) + t / (12 * N)|
      ≤ ((s2.reR : ℝ) + s1.reR) * aIm := mul_le_mul_of_nonneg_left haIm (by positivity)
  have r2 : ((s2.imR : ℝ) + s1.imR) * |-(N : ℝ) / (2 * (1 / 4 + t ^ 2)) + 1 / 2 + 1 / (24 * N)|
      ≤ ((s2.imR : ℝ) + s1.imR) * aRe := mul_le_mul_of_nonneg_left haRe (by positivity)
  rw [abs_le] at hb
  constructor
  · have : lo * 2 ^ c.P ≤ (riemannZeta (sOf t)).im * 2 ^ c.P := by linarith [hb.1]
    exact le_of_mul_le_mul_right this hP
  · have : (riemannZeta (sOf t)).im * 2 ^ c.P ≤ hi * 2 ^ c.P := by linarith [hb.2]
    exact le_of_mul_le_mul_right this hP

end ArbEcon
