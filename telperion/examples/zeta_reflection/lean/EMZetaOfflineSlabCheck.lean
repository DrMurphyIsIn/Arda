/-  EMZetaOfflineSlabCheck.lean -- lane offline: the KERNEL checker of a zero-free cell.

    The off-line evaluator run at a center `c = σc + i tc` with `p + 1` accumulators gives, after
    `N - 1` and `N` terms, balls of `S_k = Σ_{n<N} (log n)^k n^(-c)` and of `S_k + (log N)^k N^(-c)`.
    With the exact correction factor `emCorr K c N = (BreN + i BimN)/BD` (`corrDataG`) they give balls
    of the Taylor weights `W_k = S_k + (log N)^k N^(-c) emCorr K c N` of `EMZetaOfflineSlab`.

      * `wData`, `wball_sound`  -- the ball of `W_k`, scaled by `2^P BD`;
      * `sumM`, `sumM_sound`    -- `Σ_{k≥1} ‖W_k‖ rn^k rd^(p-k) (p!/k!)` from above;
      * `checkCell`, `checkCell_sound` -- ONE Boolean check (run by `decide +kernel`) proving
                                   `Σ_{k=1}^p ‖W_k‖ r^k/k! + FN/FD < ‖W_0‖`, `r = rn/rd`, the
                                   hypothesis `hmain` of `zeta_ne_zero_of_cell`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing about RH.
-/
import EMZetaOfflineSlab

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-! ## A. The Taylor weights from the evaluator's partial sums. -/

theorem Wk_eq_psumK (K N : ℕ) (hN : 1 ≤ N) (σ t : ℝ) (k : ℕ) :
    Wk K N (sOfG σ t) k = psumK σ t k (N - 1)
      + (psumK σ t k N - psumK σ t k (N - 1)) * emCorr K (sOfG σ t) N := by
  have hNm : N - 1 + 1 = N := by omega
  have hsucc := psumK_succ σ t k (N - 1)
  rw [hNm] at hsucc
  rw [hsucc]
  simp only [Wk, psumK]
  rw [hNm]
  push_cast
  ring

/-! ## B. The ball of a weight. -/

/-- `(CreN, CimN, RreN, RimN)`: the ball of `A1 + (A2 - A1)(BreN + i BimN)/BD`, scaled by `2^P BD`,
    from the balls `x1 ∋ A1`, `x2 ∋ A2`. -/
def wData (BreN BimN BD : ℤ) (x1 x2 : Acc) : ℤ × ℤ × ℤ × ℤ :=
  (((x1.reP : ℤ) - x1.reN) * BD + ((((x2.reP : ℤ) - x2.reN) - ((x1.reP : ℤ) - x1.reN))) * BreN
      - ((((x2.imP : ℤ) - x2.imN) - ((x1.imP : ℤ) - x1.imN))) * BimN,
   ((x1.imP : ℤ) - x1.imN) * BD + ((((x2.reP : ℤ) - x2.reN) - ((x1.reP : ℤ) - x1.reN))) * BimN
      + ((((x2.imP : ℤ) - x2.imN) - ((x1.imP : ℤ) - x1.imN))) * BreN,
   (x1.reR : ℤ) * BD + ((x2.reR : ℤ) + x1.reR) * (BreN.natAbs : ℤ) + ((x2.imR : ℤ) + x1.imR) * (BimN.natAbs : ℤ),
   (x1.imR : ℤ) * BD + ((x2.reR : ℤ) + x1.reR) * (BimN.natAbs : ℤ) + ((x2.imR : ℤ) + x1.imR) * (BreN.natAbs : ℤ))

/-- The upper bound `|CreN| + RreN + |CimN| + RimN` of `‖W‖ 2^P BD`. -/
def wUpper (d : ℤ × ℤ × ℤ × ℤ) : ℤ := (d.1.natAbs : ℤ) + d.2.2.1 + (d.2.1.natAbs : ℤ) + d.2.2.2

theorem wball_sound (P : ℕ) (A1 A2 : ℂ) (x1 x2 : Acc) (h1 : AccOK P A1 x1) (h2 : AccOK P A2 x2)
    (BreN BimN BD : ℤ) (hBD : (0 : ℝ) < BD) (B : ℂ) (hBre : B.re = (BreN : ℝ) / BD)
    (hBim : B.im = (BimN : ℝ) / BD) :
    |(A1 + (A2 - A1) * B).re * 2 ^ P * BD - ((wData BreN BimN BD x1 x2).1 : ℝ)|
        ≤ ((wData BreN BimN BD x1 x2).2.2.1 : ℝ) ∧
    |(A1 + (A2 - A1) * B).im * 2 ^ P * BD - ((wData BreN BimN BD x1 x2).2.1 : ℝ)|
        ≤ ((wData BreN BimN BD x1 x2).2.2.2 : ℝ) := by
  obtain ⟨hre1, him1⟩ := h1
  obtain ⟨hre2, him2⟩ := h2
  have hBDne : (BD : ℝ) ≠ 0 := ne_of_gt hBD
  simp only [wData]
  push_cast
  have hzre : |(A2 - A1).re * 2 ^ P - ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)))|
      ≤ (x2.reR : ℝ) + x1.reR := by
    rw [Complex.sub_re]
    have e : (A2.re - A1.re) * 2 ^ P - ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)))
        = (A2.re * 2 ^ P - ((x2.reP : ℝ) - x2.reN)) - (A1.re * 2 ^ P - ((x1.reP : ℝ) - x1.reN)) := by ring
    rw [e]; exact le_trans (abs_sub _ _) (add_le_add hre2 hre1)
  have hzim : |(A2 - A1).im * 2 ^ P - ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)))|
      ≤ (x2.imR : ℝ) + x1.imR := by
    rw [Complex.sub_im]
    have e : (A2.im - A1.im) * 2 ^ P - ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)))
        = (A2.im * 2 ^ P - ((x2.imP : ℝ) - x2.imN)) - (A1.im * 2 ^ P - ((x1.imP : ℝ) - x1.imN)) := by ring
    rw [e]; exact le_trans (abs_sub _ _) (add_le_add him2 him1)
  set u1 := A1.re * 2 ^ P - ((x1.reP : ℝ) - x1.reN) with hu1
  set v1 := A1.im * 2 ^ P - ((x1.imP : ℝ) - x1.imN) with hv1
  set ua := (A2 - A1).re * 2 ^ P - ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN))) with hua
  set va := (A2 - A1).im * 2 ^ P - ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN))) with hva
  have hWre : (A1 + (A2 - A1) * B).re = A1.re + (A2 - A1).re * B.re - (A2 - A1).im * B.im := by
    simp [Complex.add_re, Complex.mul_re]; ring
  have hWim : (A1 + (A2 - A1) * B).im = A1.im + (A2 - A1).re * B.im + (A2 - A1).im * B.re := by
    simp [Complex.add_im, Complex.mul_im]; ring
  rw [hWre, hWim, hBre, hBim]
  constructor
  · have e : (A1.re + (A2 - A1).re * ((BreN : ℝ) / BD) - (A2 - A1).im * ((BimN : ℝ) / BD)) * 2 ^ P * BD
        - ((((x1.reP : ℝ) - x1.reN) * BD + ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN))) * BreN
          - ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN))) * BimN))
        = u1 * BD + ua * BreN - va * BimN := by
      rw [hu1, hua, hva]; field_simp; ring
    rw [e]
    have t1 : |u1 * BD| ≤ x1.reR * BD := by
      rw [abs_mul, abs_of_pos hBD]; exact mul_le_mul_of_nonneg_right hre1 hBD.le
    have t2 : |ua * BreN| ≤ ((x2.reR : ℝ) + x1.reR) * |(BreN : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hzre (abs_nonneg _)
    have t3 : |va * BimN| ≤ ((x2.imR : ℝ) + x1.imR) * |(BimN : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hzim (abs_nonneg _)
    have q1 := abs_sub (u1 * BD + ua * BreN) (va * BimN)
    have q2 := abs_add_le (u1 * BD) (ua * BreN)
    linarith
  · have e : (A1.im + (A2 - A1).re * ((BimN : ℝ) / BD) + (A2 - A1).im * ((BreN : ℝ) / BD)) * 2 ^ P * BD
        - ((((x1.imP : ℝ) - x1.imN) * BD + ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN))) * BimN
          + ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN))) * BreN))
        = v1 * BD + ua * BimN + va * BreN := by
      rw [hv1, hua, hva]; field_simp; ring
    rw [e]
    have t1 : |v1 * BD| ≤ x1.imR * BD := by
      rw [abs_mul, abs_of_pos hBD]; exact mul_le_mul_of_nonneg_right him1 hBD.le
    have t2 : |ua * BimN| ≤ ((x2.reR : ℝ) + x1.reR) * |(BimN : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hzre (abs_nonneg _)
    have t3 : |va * BreN| ≤ ((x2.imR : ℝ) + x1.imR) * |(BreN : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hzim (abs_nonneg _)
    have q1 := abs_add_le (v1 * BD + ua * BimN) (va * BreN)
    have q2 := abs_add_le (v1 * BD) (ua * BimN)
    linarith

theorem wUpper_sound (P : ℕ) (W : ℂ) (BD : ℝ) (hBD : 0 < BD) (d : ℤ × ℤ × ℤ × ℤ)
    (hre : |W.re * 2 ^ P * BD - (d.1 : ℝ)| ≤ (d.2.2.1 : ℝ))
    (him : |W.im * 2 ^ P * BD - (d.2.1 : ℝ)| ≤ (d.2.2.2 : ℝ)) :
    ‖W‖ * 2 ^ P * BD ≤ (wUpper d : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hk : (0 : ℝ) < 2 ^ P * BD := by positivity
  have hn := Complex.norm_le_abs_re_add_abs_im W
  have e1 : |W.re| * (2 ^ P * BD) = |W.re * 2 ^ P * BD| := by
    rw [abs_mul, abs_mul, abs_of_pos hP, abs_of_pos hBD]; ring
  have e2 : |W.im| * (2 ^ P * BD) = |W.im * 2 ^ P * BD| := by
    rw [abs_mul, abs_mul, abs_of_pos hP, abs_of_pos hBD]; ring
  have a1 : |W.re * 2 ^ P * BD| ≤ |(d.1 : ℝ)| + d.2.2.1 := by
    have := abs_sub_abs_le_abs_sub (W.re * 2 ^ P * BD) (d.1 : ℝ); linarith
  have a2 : |W.im * 2 ^ P * BD| ≤ |(d.2.1 : ℝ)| + d.2.2.2 := by
    have := abs_sub_abs_le_abs_sub (W.im * 2 ^ P * BD) (d.2.1 : ℝ); linarith
  have hw : (wUpper d : ℝ) = |(d.1 : ℝ)| + d.2.2.1 + |(d.2.1 : ℝ)| + d.2.2.2 := by
    simp only [wUpper]; push_cast; rfl
  rw [hw]
  calc ‖W‖ * 2 ^ P * BD = ‖W‖ * (2 ^ P * BD) := by ring
    _ ≤ (|W.re| + |W.im|) * (2 ^ P * BD) := mul_le_mul_of_nonneg_right hn hk.le
    _ = |W.re * 2 ^ P * BD| + |W.im * 2 ^ P * BD| := by rw [add_mul, e1, e2]
    _ ≤ _ := by linarith

/-! ## C. The weighted sum over `k ≥ 1`. -/

/-- `Σ_{j ≥ k} wUpper(W_j) rn^j rd^(p-j) (p!/j!)` over the paired accumulator lists. -/
def sumM (BreN BimN BD : ℤ) (rn rd p : ℕ) : ℕ → List Acc → List Acc → ℤ
  | k, x1 :: xs1, x2 :: xs2 =>
    wUpper (wData BreN BimN BD x1 x2) * (rn : ℤ) ^ k * (rd : ℤ) ^ (p - k) * ((p ! / k ! : ℕ) : ℤ)
      + sumM BreN BimN BD rn rd p (k + 1) xs1 xs2
  | _, _, _ => 0

theorem sumM_sound (P : ℕ) (f1 f2 : ℕ → ℂ) (B : ℂ) (BreN BimN BD : ℤ) (hBD : (0 : ℝ) < BD)
    (hBre : B.re = (BreN : ℝ) / BD) (hBim : B.im = (BimN : ℝ) / BD) (rn rd p : ℕ) :
    ∀ (m k : ℕ) (xs1 xs2 : List Acc), xs1.length = m → xs2.length = m →
      AccsOK P f1 k xs1 → AccsOK P f2 k xs2 →
      ∑ j ∈ Finset.Ico k (k + m), ‖f1 j + (f2 j - f1 j) * B‖ * 2 ^ P * BD
          * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))
        ≤ (sumM BreN BimN BD rn rd p k xs1 xs2 : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro k xs1 xs2 hl1 hl2 _ _
    rw [List.length_eq_zero_iff] at hl1 hl2
    subst hl1; subst hl2
    simp [sumM]
  | succ m ih =>
    intro k xs1 xs2 hl1 hl2 hA1 hA2
    match xs1, xs2, hl1, hl2, hA1, hA2 with
    | x1 :: ys1, x2 :: ys2, hl1, hl2, hA1, hA2 =>
      obtain ⟨hx1, hy1⟩ := hA1
      obtain ⟨hx2, hy2⟩ := hA2
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1 hl2
      have hrec := ih (k + 1) ys1 ys2 hl1 hl2 hy1 hy2
      have hb := wball_sound P (f1 k) (f2 k) x1 x2 hx1 hx2 BreN BimN BD hBD B hBre hBim
      have hu := wUpper_sound P (f1 k + (f2 k - f1 k) * B) BD hBD _ hb.1 hb.2
      have hfac : (0 : ℝ) ≤ (rn : ℝ) ^ k * (rd : ℝ) ^ (p - k) * ((p ! / k ! : ℕ) : ℝ) := by positivity
      rw [show k + (m + 1) = (k + 1) + m by ring, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have hs : (sumM BreN BimN BD rn rd p k (x1 :: ys1) (x2 :: ys2) : ℝ)
          = (wUpper (wData BreN BimN BD x1 x2) : ℝ) * ((rn : ℝ) ^ k * (rd : ℝ) ^ (p - k)
              * ((p ! / k ! : ℕ) : ℝ)) + (sumM BreN BimN BD rn rd p (k + 1) ys1 ys2 : ℝ) := by
        simp only [sumM, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]; ring
      rw [hs]
      have := mul_le_mul_of_nonneg_right hu hfac
      linarith

/-! ## D. The cell checker. -/

/-- The right side `(R0re + R0im) T + (Σ_{k≥1} …) FD + FN 2^P BD rd^p p!` of the cell check,
    `T = rd^p p! FD` (all scaled by `2^P BD rd^p p! FD`). -/
def cellRHS (c : Cfg) (o : OCfg) (K N p : ℕ) (x1 x2 : Acc) (ys1 ys2 : List Acc) (rn rd FN FD : ℕ) : ℤ :=
  (((wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2).2.2.1
    + (wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2).2.2.2)
    * ((rd : ℤ) ^ p * ((p ! : ℕ) : ℤ) * FD))
  + sumM (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 rn rd p 1 ys1 ys2 * FD
  + FN * 2 ^ c.P * (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 * (rd : ℤ) ^ p * ((p ! : ℕ) : ℤ)

/-- The left side `(C0re² + C0im²) T²` of the cell check. -/
def cellLHS (c : Cfg) (o : OCfg) (K N p : ℕ) (x1 x2 : Acc) (rd FD : ℕ) : ℤ :=
  ((wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2).1 ^ 2
    + (wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2).2.1 ^ 2)
  * ((rd : ℤ) ^ p * ((p ! : ℕ) : ℤ) * FD) ^ 2

/-- **The kernel cell check.**  `xs1`, `xs2`: the `p + 1` accumulators after `N - 1` and `N` terms at
    `c = σ + i t`; `r = rn/rd`; `F = FN/FD`.  Checks `Σ_{k=1}^p ‖W_k‖ r^k/k! + F < ‖W_0‖` by comparing
    squares, everything multiplied through by `2^P BD rd^p p! FD`. -/
def checkCell (c : Cfg) (o : OCfg) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ) : Bool :=
  match xs1, xs2 with
  | x1 :: ys1, x2 :: ys2 =>
    Nat.ble 1 K && Nat.ble K 6 && Nat.ble 2 N && Nat.ble 1 rd && Nat.ble 1 FD && Nat.ble 1 o.q &&
      Nat.ble 1 c.tn && Nat.beq ys1.length p && Nat.beq ys2.length p &&
      decide (0 ≤ cellRHS c o K N p x1 x2 ys1 ys2 rn rd FN FD) &&
      decide (cellRHS c o K N p x1 x2 ys1 ys2 rn rd FN FD * cellRHS c o K N p x1 x2 ys1 ys2 rn rd FN FD
        < cellLHS c o K N p x1 x2 rd FD)
  | _, _ => false

set_option maxHeartbeats 2000000 in
theorem checkCell_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ)
    (h1 : AccsOK c.P (fun k => psumK σ t k (N - 1)) 0 xs1)
    (h2 : AccsOK c.P (fun k => psumK σ t k N) 0 xs2)
    (hc : checkCell c o K N p xs1 xs2 rn rd FN FD = true) :
    ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N (sOfG σ t) k‖ * ((rn : ℝ) / rd) ^ k / (k ! : ℝ)
      + (FN : ℝ) / FD < ‖Wk K N (sOfG σ t) 0‖ := by
  match xs1, xs2, h1, h2, hc with
  | x1 :: ys1, x2 :: ys2, h1, h2, hc =>
    simp only [checkCell, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, hrd⟩, hFD⟩, hq1⟩, htn1⟩, hl1⟩, hl2⟩, hRHS0⟩, hmainZ⟩ := hc
    have hl1' : ys1.length = p := Nat.eq_of_beq_eq_true hl1
    have hl2' : ys2.length = p := Nat.eq_of_beq_eq_true hl2
    obtain ⟨hx1, hy1⟩ := h1
    obtain ⟨hx2, hy2⟩ := h2
    -- the correction factor
    set u : ℕ := 2 ^ c.tq with hudef
    have hu : 0 < u := Nat.two_pow_pos _
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    have ht' : t = (c.tn : ℝ) / u := by rw [ht, hudef]; push_cast; ring
    have hσ' : σ = (((o.a : ℤ) - o.b : ℤ) : ℝ) / o.q := by rw [hσ]; push_cast; ring
    obtain ⟨hcre, hcim⟩ := corr_eqG K ((o.a : ℤ) - o.b) o.q u c.tn N hK1 hK6 (by omega) hu
      (by omega) (by omega) σ t hσ' ht'
    set cd := corrDataG K ((o.a : ℤ) - o.b) o.q u c.tn N with hcd
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hqR : (0 : ℝ) < o.q := by exact_mod_cast (show 0 < o.q by omega)
    have htnR : (0 : ℝ) < c.tn := by exact_mod_cast (show 0 < c.tn by omega)
    have hBDpos : (0 : ℝ) < (cd.2.2 : ℝ) := by
      have e : (cd.2.2 : ℝ) = 2 * (((((o.a : ℤ) - o.b : ℤ) : ℝ) - o.q) ^ 2 * (u : ℝ) ^ 2
          + (c.tn : ℝ) ^ 2 * (o.q : ℝ) ^ 2) * ((ArbEcon.OrderK.Lbeta : ℝ) * ((o.q : ℝ) * u * N) ^ (2 * K - 1)) := by
        simp only [hcd, corrDataG]; push_cast; ring
      rw [e]
      have hL : (0 : ℝ) < (ArbEcon.OrderK.Lbeta : ℝ) := by norm_num [ArbEcon.OrderK.Lbeta]
      positivity
    set B := emCorr K (sOfG σ t) N with hB
    have hBre : B.re = (cd.1 : ℝ) / cd.2.2 := by rw [← hcre]; exact (emCorr_re_im K σ t N).1
    have hBim : B.im = (cd.2.1 : ℝ) / cd.2.2 := by rw [← hcim]; exact (emCorr_re_im K σ t N).2
    -- the weights
    have hW : ∀ k, Wk K N (sOfG σ t) k = psumK σ t k (N - 1) + (psumK σ t k N - psumK σ t k (N - 1)) * B :=
      fun k => Wk_eq_psumK K N (by omega) σ t k
    simp only [hW]
    set S : ℝ := 2 ^ c.P * cd.2.2 with hS
    have hP : (0 : ℝ) < 2 ^ c.P := by positivity
    have hSpos : 0 < S := by positivity
    -- the k = 0 ball
    have hb0 := wball_sound c.P (psumK σ t 0 (N - 1)) (psumK σ t 0 N) x1 x2 hx1 hx2 cd.1 cd.2.1 cd.2.2
      hBDpos B hBre hBim
    set d0 := wData cd.1 cd.2.1 cd.2.2 x1 x2 with hd0
    set W0 := psumK σ t 0 (N - 1) + (psumK σ t 0 N - psumK σ t 0 (N - 1)) * B with hW0
    set Csq : ℝ := (d0.1 : ℝ) ^ 2 + (d0.2.1 : ℝ) ^ 2 with hCsq
    set R0 : ℝ := (d0.2.2.1 : ℝ) + d0.2.2.2 with hR0
    -- ‖W0‖ S ≥ ‖center‖ - R0
    have hcenter : Real.sqrt Csq - R0 ≤ ‖W0‖ * S := by
      set Z : ℂ := W0 * (S : ℂ) with hZ
      set C : ℂ := (d0.1 : ℂ) + (d0.2.1 : ℂ) * Complex.I with hC
      have hZre : Z.re = W0.re * 2 ^ c.P * cd.2.2 := by
        rw [hZ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hS]; ring
      have hZim : Z.im = W0.im * 2 ^ c.P * cd.2.2 := by
        rw [hZ, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hS]; ring
      have hCre : C.re = d0.1 := by simp [hC]
      have hCim : C.im = d0.2.1 := by simp [hC]
      have hnC : ‖C‖ = Real.sqrt Csq := by
        rw [Complex.norm_eq_sqrt_sq_add_sq, hCre, hCim]
      have hdiff : ‖Z - C‖ ≤ R0 := by
        refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
        rw [Complex.sub_re, Complex.sub_im, hZre, hZim, hCre, hCim]
        exact add_le_add hb0.1 hb0.2
      have hnZ : ‖Z‖ = ‖W0‖ * S := by
        rw [hZ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hSpos.le]
      have htri : ‖C‖ ≤ ‖Z‖ + ‖Z - C‖ := by
        have := norm_sub_norm_le C Z
        rw [norm_sub_rev] at this
        linarith
      rw [← hnC, ← hnZ]
      linarith
    -- the k ≥ 1 sum
    have hsum := sumM_sound c.P (fun k => psumK σ t k (N - 1)) (fun k => psumK σ t k N) B cd.1 cd.2.1
      cd.2.2 hBDpos hBre hBim rn rd p p 1 ys1 ys2 hl1' hl2' hy1 hy2
    rw [show 1 + p = p + 1 by ring] at hsum
    set Msum : ℝ := (sumM cd.1 cd.2.1 cd.2.2 rn rd p 1 ys1 ys2 : ℝ) with hMsum
    -- the integer inequalities, cast
    set T : ℝ := (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) * FD with hT
    have hrdR : (0 : ℝ) < rd := by exact_mod_cast (show 0 < rd by omega)
    have hFDR : (0 : ℝ) < FD := by exact_mod_cast (show 0 < FD by omega)
    have hpf : (0 : ℝ) < ((p ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos p
    have hTpos : 0 < T := by positivity
    set RHS : ℝ := R0 * T + Msum * FD + (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) with hRHSdef
    have hRHScast : ((cellRHS c o K N p x1 x2 ys1 ys2 rn rd FN FD : ℤ) : ℝ) = RHS := by
      simp only [cellRHS, hRHSdef, hR0, hMsum, hS, hT, hd0, hcd, hudef]
      push_cast; ring
    have hLHScast : ((cellLHS c o K N p x1 x2 rd FD : ℤ) : ℝ) = Csq * T ^ 2 := by
      simp only [cellLHS, hCsq, hT, hd0, hcd, hudef]
      push_cast; ring
    have hRHS0R : 0 ≤ RHS := by
      rw [← hRHScast]; exact_mod_cast hRHS0
    have hmainR : RHS * RHS < Csq * T ^ 2 := by
      rw [← hRHScast, ← hLHScast]; exact_mod_cast hmainZ
    have hCsq0 : 0 ≤ Csq := by positivity
    have hsq : RHS < Real.sqrt Csq * T := by
      have hsq2 : RHS ^ 2 < Csq * T ^ 2 := by rw [sq]; exact hmainR
      have h1 : RHS < Real.sqrt (Csq * T ^ 2) := (Real.lt_sqrt hRHS0R).mpr hsq2
      rwa [Real.sqrt_mul hCsq0, Real.sqrt_sq hTpos.le] at h1
    -- assemble:  ‖W0‖ S T > FD Σ_k … + FN S rd^p p!
    have h2' := mul_le_mul_of_nonneg_right hcenter hTpos.le
    have h1' := mul_le_mul_of_nonneg_right hsum hFDR.le
    have hkey : (∑ j ∈ Finset.Ico 1 (p + 1), ‖psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B‖
          * 2 ^ c.P * cd.2.2 * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))) * FD
        + (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) < ‖W0‖ * S * T := by
      have e1 : (Real.sqrt Csq - R0) * T = Real.sqrt Csq * T - R0 * T := by ring
      rw [e1] at h2'
      linarith
    -- divide by S T = S rd^p p! FD
    have hterm : ∀ j ∈ Finset.Ico 1 (p + 1),
        ‖psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B‖ * 2 ^ c.P * cd.2.2
          * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ)) * FD
        = (‖psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B‖ * ((rn : ℝ) / rd) ^ j
            / (j ! : ℝ)) * (S * T) := by
      intro j hj
      have hjp : j ≤ p := by have := Finset.mem_Ico.mp hj; omega
      have hdvd : j ! ∣ p ! := Nat.factorial_dvd_factorial hjp
      have hjf : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
      have hcast : ((p ! / j ! : ℕ) : ℝ) = ((p ! : ℕ) : ℝ) / (j ! : ℝ) := Nat.cast_div hdvd (ne_of_gt hjf)
      have hpow : (rd : ℝ) ^ p = (rd : ℝ) ^ (p - j) * (rd : ℝ) ^ j := by
        rw [← pow_add]; congr 1; omega
      rw [hcast, hT, hS, hpow, div_pow]
      field_simp
    rw [Finset.sum_mul] at hkey
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul] at hkey
    have hST : 0 < S * T := by positivity
    have e3 : (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) = (FN : ℝ) / FD * (S * T) := by
      rw [hT]; field_simp
    rw [e3, ← add_mul, show ‖W0‖ * S * T = ‖W0‖ * (S * T) by ring] at hkey
    exact lt_of_mul_lt_mul_right hkey hST.le

end Off

end ArbEcon
