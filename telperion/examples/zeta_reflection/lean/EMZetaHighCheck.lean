/-  EMZetaHighCheck.lean -- a KERNEL-ONLY assembly for the order-(2K+1) Euler-Maclaurin enclosure
    of ζ(1/2 + i t) (lane emhigh, production format).

    `EMZetaHighEval.zetaK_re_bounds` turns the evaluator invariants into Re/Im ζ bounds, but an
    instance then discharges its rational side conditions (the correction factor `B_K(t, N)`, the
    remainder constant, the final inequalities) with `norm_num` on 60-digit rationals: about 3 s of
    tactic interpretation and 1.3 MB of proof term per evaluation.  At the h280000 scale (445,947
    sign evaluations) that is about 400 core-hours of elaboration and 0.6 TB of oleans.

    This file replaces all of it by ONE Boolean checker `checkK`, run by `decide +kernel`, over plain
    `Nat`/`Int` arithmetic, and ONE soundness theorem `checkK_sound`, proved once:
      * `valid64`                  -- the P = 64 evaluator configuration `EMZetaHighCfg64.cfg64`
                                      (lnbig = sqbig = 256) as a function of the height `t = tn / 2^tq`,
                                      validated ONCE for all heights (no per-instance `norm_num`).
      * `betaN`, `Lbeta`, `betaN_spec` -- `B_{i+2}/(i+2)! = betaN i / Lβ`, `Lβ = 2730·12!`, `i ≤ 10`.
      * `gpoch`, `pochRI_eq_gpoch`  -- the Gaussian-integer rising factorial `(2u)^k (1/2 + i tn/u)_k`.
      * `corrData`, `corr_eq`       -- the exact correction factor `emCorr K (1/2 + i t) N` as
                                      `(BreN + i BimN) / BD` with integers computed in the kernel.
      * `pnK`, `pochNormSq_eq_pnK`  -- the remainder numerator `Π_{j<k} ((2j+1)² u² + 4 tn²)`.
      * `remEven`, `remOdd` (+ `_sound`) -- the remainder as `EN/ED` in integers, even-saw
                                      (`em_line_remainder_le`) or odd-saw (`em_line_remainder_odd_le`,
                                      π replaced by `3.141592 < π < 3.141593`, about 7 percent fewer terms).
      * `checkCore`, `checkCore_sound` -- the four final inequalities for ANY remainder `EN/ED`.
      * `checkK`, `checkK_sound`    -- the checker (`odd` flag) and its soundness: `checkK … = true`
                                      gives `reLo/D ≤ Re ζ(1/2+it) ≤ reHi/D` and the same for Im.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/
import EMZetaHighEval
import EMZetaHighCfg64

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace OrderK

/-! ## A. The P = 64 configuration (`EMZetaHighCfg64.cfg64`), validated once for every height. -/

/-- `cfg64` is a valid evaluator configuration at EVERY height (proved once). -/
theorem valid64 (tn tq : ℕ) (t : ℝ) (ht : t = (tn : ℝ) / 2 ^ tq) : Valid (cfg64 tn tq) t 9 where
  one_eq := by show (18446744073709551616 : ℕ) = 2 ^ 64; norm_num
  two1_eq := by show (36893488147419103232 : ℕ) = 2 ^ (64 + 1); norm_num
  oneSq_eq := by show (340282366920938463463374607431768211456 : ℕ) = 2 ^ (2 * 64); norm_num
  t_eq := ht
  pi_ball := by
    show |Real.pi / 2 * 2 ^ (64 : ℕ) - ((28976077832308491369 : ℕ) : ℝ)| ≤ ((2 : ℕ) : ℝ)
    have h1 := Real.pi_gt_d20
    have h2 := Real.pi_lt_d20
    rw [abs_le]; constructor <;> norm_num <;> linarith
  umax_le := by show (14987979559889010688 : ℕ) * 16 ≤ 13 * 2 ^ 64; norm_num
  dcos_eq := by
    show [5644703686555122794496, 4427218577690292387840, 3357307421415138394112,
      2434970217729660813312, 1660206966633859645440, 1033017668127734890496, 553402322211286548480,
      221360928884514619392, 36893488147419103232] = (divList fcos 9).map (fun d : ℕ => 18446744073709551616 * d)
    decide
  dsin_eq := by
    show [6308786473208666652672, 5017514388048998039552, 3873816255479005839360,
      2877692075498690052096, 2029141848108050677760, 1328165573307087716352, 774763251095801167872,
      368934881474191032320, 110680464442257309696] = (divList fsin 9).map (fun d : ℕ => 18446744073709551616 * d)
    decide
  tau_ok := by
    show (2 : ℝ) ^ (64 : ℕ) * ArbEcon.taylorBnd 9 ≤ ((1 : ℕ) : ℝ)
    unfold ArbEcon.taylorBnd; norm_num [Nat.factorial]
  hc_eq := fun _ => rfl
  hs_eq := fun _ => rfl
  lnf_eq := fun _ => rfl

/-! ## B. Bernoulli data over one common denominator. -/

/-- `Lβ = 2730 · 12!`, a common denominator of `B_{i+2}/(i+2)!` for `i ≤ 10`. -/
def Lbeta : ℕ := 1307674368000

/-- `B_{i+2}/(i+2)! = betaN i / Lβ` (`i ≤ 10`); odd Bernoulli numbers past `B_1` vanish. -/
def betaN : ℕ → ℤ
  | 0 => 108972864000
  | 2 => -1816214400
  | 4 => 43243200
  | 6 => -1081080
  | 8 => 27300
  | 10 => -691
  | _ => 0

theorem betaN_spec (i : ℕ) (hi : i ≤ 10) :
    (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) = (betaN i : ℝ) / (Lbeta : ℝ) := by
  obtain ⟨h3, h5, h7, h9, h11, _⟩ := bernoulli_odd_vanish
  interval_cases i <;>
    simp [betaN, Lbeta, Nat.factorial, bernoulli_two, bernoulli_four', bernoulli_six',
      bernoulli_eight', bernoulli_ten', bernoulli_twelve', h3, h5, h7, h9, h11] <;> norm_num

/-! ## C. The correction factor in exact integer arithmetic. -/

/-- Gaussian-integer rising factorial: `G_k = (2u)^k (1/2 + i tn/u)_k` with `U = u`, `T2 = 2 tn`
    (`G_{k+1} = G_k · ((2k+1)U + i T2)`). -/
def gpoch (U T2 : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 =>
    match gpoch U T2 k with
    | (x, y) => (x * ((2 * k + 1) * U) - y * T2, x * T2 + y * ((2 * k + 1) * U))

theorem gpoch_succ (U T2 : ℤ) (k : ℕ) :
    gpoch U T2 (k + 1) = ((gpoch U T2 k).1 * ((2 * k + 1) * U) - (gpoch U T2 k).2 * T2,
      (gpoch U T2 k).1 * T2 + (gpoch U T2 k).2 * ((2 * k + 1) * U)) := by
  show (match gpoch U T2 k with
    | (x, y) => (x * ((2 * k + 1) * U) - y * T2, x * T2 + y * ((2 * k + 1) * U))) = _
  rcases gpoch U T2 k with ⟨x, y⟩
  rfl

/-- `pochRI (1/2) t k = G_k / (2u)^k` for `t = tn / u`. -/
theorem pochRI_eq_gpoch (u tn : ℕ) (hu : 0 < u) (t : ℝ) (ht : t = (tn : ℝ) / u) (k : ℕ) :
    (pochRI (1 / 2) t k).1 = ((gpoch u (2 * tn) k).1 : ℝ) / (2 * u) ^ k ∧
    (pochRI (1 / 2) t k).2 = ((gpoch u (2 * tn) k).2 : ℝ) / (2 * u) ^ k := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  induction k with
  | zero => simp [pochRI, gpoch]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [gpoch_succ]
    simp only [pochRI]
    rw [h1, h2, ht]
    push_cast
    have hne : (2 * (u : ℝ)) ^ k ≠ 0 := by positivity
    constructor <;> field_simp <;> ring

/-- `Σ_{i<j} βN_i · G_{i+1} · W^(M-1-i)` (real and imaginary parts). -/
def gsum (U T2 W : ℤ) (M : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | j + 1 => ((gsum U T2 W M j).1 + betaN j * (gpoch U T2 (j + 1)).1 * W ^ (M - 1 - j),
              (gsum U T2 W M j).2 + betaN j * (gpoch U T2 (j + 1)).2 * W ^ (M - 1 - j))

theorem gsum_eq (U T2 W : ℤ) (M j : ℕ) :
    ((gsum U T2 W M j).1 : ℝ)
        = ∑ i ∈ Finset.range j, (betaN i : ℝ) * ((gpoch U T2 (i + 1)).1 : ℝ) * (W : ℝ) ^ (M - 1 - i) ∧
    ((gsum U T2 W M j).2 : ℝ)
        = ∑ i ∈ Finset.range j, (betaN i : ℝ) * ((gpoch U T2 (i + 1)).2 : ℝ) * (W : ℝ) ^ (M - 1 - i) := by
  induction j with
  | zero => simp [gsum]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [gsum, Finset.sum_range_succ]
    push_cast
    rw [h1, h2]
    exact ⟨rfl, rfl⟩

/-- The exact correction factor `emCorr K (1/2 + i tn/u) N = (BreN + i BimN) / BD`:
    returns `(BreN, BimN, BD)`. -/
def corrData (K u tn N : ℕ) : ℤ × ℤ × ℤ :=
  let U : ℤ := u
  let T2 : ℤ := 2 * tn
  let M := 2 * K - 1
  let W : ℤ := 2 * u * N
  let q : ℤ := U * U + T2 * T2
  let base : ℤ := Lbeta * W ^ M
  let S := gsum U T2 W M M
  (-(4 * u * N) * U * base + q * base + 2 * q * S.1,
   -(4 * u * N) * T2 * base + 2 * q * S.2,
   2 * q * base)

theorem corr_eq (K u tn N : ℕ) (hK1 : 1 ≤ K) (hK6 : K ≤ 6) (hu : 0 < u) (hN : 1 ≤ N) (t : ℝ)
    (ht : t = (tn : ℝ) / u) :
    emCorrRe K (1 / 2) t N = ((corrData K u tn N).1 : ℝ) / ((corrData K u tn N).2.2 : ℝ) ∧
    emCorrIm K (1 / 2) t N = ((corrData K u tn N).2.1 : ℝ) / ((corrData K u tn N).2.2 : ℝ) := by
  set M := 2 * K - 1 with hM
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hWR : (0 : ℝ) < 2 * u * N := by positivity
  have hq : (0 : ℝ) < (u : ℝ) * u + (2 * tn) * (2 * tn) := by positivity
  have hL : (0 : ℝ) < (Lbeta : ℝ) := by norm_num [Lbeta]
  obtain ⟨hS1, hS2⟩ := gsum_eq (u : ℤ) (2 * tn) (2 * u * N) M M
  -- each correction term, rewritten over the common denominator Lβ W^M
  have key : ∀ (sel : ℕ → ℤ) (p : ℕ → ℝ),
      (∀ i, i < M → p (i + 1) = (sel (i + 1) : ℝ) / (2 * u) ^ (i + 1)) →
      (∑ i ∈ Finset.range M,
          (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * p (i + 1))
        = (∑ i ∈ Finset.range M, (betaN i : ℝ) * (sel (i + 1) : ℝ) * ((2 * u * N : ℤ) : ℝ) ^ (M - 1 - i))
            / ((Lbeta : ℝ) * ((2 * u * N : ℤ) : ℝ) ^ M) := by
    intro sel p hp
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hiM : i < M := Finset.mem_range.mp hi
    have hi10 : i ≤ 10 := by omega
    rw [betaN_spec i hi10, hp i hiM]
    push_cast
    have hpow : (2 * (u : ℝ) * N) ^ M = (2 * (u : ℝ) * N) ^ (M - 1 - i) * (2 * (u : ℝ) * N) ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    have h1 : (2 * (u : ℝ) * N) ^ (M - 1 - i) ≠ 0 := by positivity
    have h2 : (2 * (u : ℝ)) ^ (i + 1) ≠ 0 := by positivity
    have h3 : (N : ℝ) ^ (i + 1) ≠ 0 := by positivity
    rw [mul_pow, mul_pow]
    field_simp
    ring
  have hpR := fun i (_ : i < M) => (pochRI_eq_gpoch u tn hu t ht (i + 1)).1
  have hpI := fun i (_ : i < M) => (pochRI_eq_gpoch u tn hu t ht (i + 1)).2
  have kR := key (fun k => (gpoch u (2 * tn) k).1) (fun k => (pochRI (1 / 2) t k).1) hpR
  have kI := key (fun k => (gpoch u (2 * tn) k).2) (fun k => (pochRI (1 / 2) t k).2) hpI
  constructor
  · simp only [emCorrRe]
    rw [← hM, kR]
    simp only [corrData]
    rw [← hM]
    push_cast at hS1 ⊢
    rw [← hS1]
    subst ht
    field_simp
    ring
  · simp only [emCorrIm]
    rw [← hM, kI]
    simp only [corrData]
    rw [← hM]
    push_cast at hS2 ⊢
    rw [← hS2]
    subst ht
    field_simp
    ring

/-! ## D. The remainder numerator. -/

/-- `Π_{j<k} ((2j+1)² u² + 4 tn²)`. -/
def pnK (u tn : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => pnK u tn k * ((2 * k + 1) ^ 2 * u ^ 2 + 4 * tn ^ 2)

theorem pochNormSq_eq_pnK (u tn : ℕ) (hu : 0 < u) (t : ℝ) (ht : t = (tn : ℝ) / u) (k : ℕ) :
    pochNormSq (1 / 2) t k = (pnK u tn k : ℝ) / (2 * u) ^ (2 * k) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  induction k with
  | zero => simp [pochNormSq, pnK]
  | succ k ih =>
    rw [pochNormSq, ih, pnK]
    push_cast
    subst ht
    have hne : (2 * (u : ℝ)) ^ (2 * k) ≠ 0 := by positivity
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    field_simp
    ring

/-! ## E. The remainder certificates (even and odd saw forms). -/

/-- Even-saw remainder certificate: `(ok, EN, ED)` with `E = EN/ED`, `E` the bound of
    `em_line_remainder_le` at `Q/(2u)^(2K)` (`ok`: `0 < r`, `r² ≤ N`, `pnK(2K) ≤ Q²`). -/
def remEven (K u tn N Q r : ℕ) : Bool × ℤ × ℤ :=
  (Nat.ble 1 r && Nat.ble (r * r) N && Nat.ble (pnK u tn (2 * K)) (Q * Q),
   2 * ((betaN (2 * K - 2)).natAbs : ℤ) * Q,
   (Lbeta : ℤ) * (2 * u) ^ (2 * K) * N ^ (2 * K - 1) * r * (4 * K - 1))

/-- Odd-saw remainder certificate, with `6.283184 < 2π` and `π < 3.141593` (Mathlib
    `pi_gt_d6`/`pi_lt_d6`): `E ≤ 4 A 1000000^(2K+1) Q / (6·10^12 2^(2K−1) 6283184^(2K+1) (2u)^(2K+1) N^(2K)
    r (4K+1))`, `A = 6·10^12 2^(2K−1) + 3141593² − 6·10^12` (`ok`: `0 < r`, `r² ≤ N`,
    `pnK(2K+1) ≤ Q²`). -/
def remOdd (K u tn N Q r : ℕ) : Bool × ℤ × ℤ :=
  (Nat.ble 1 r && Nat.ble (r * r) N && Nat.ble (pnK u tn (2 * K + 1)) (Q * Q),
   4 * (6000000000000 * 2 ^ (2 * K - 1) + 9869606577649 - 6000000000000) * 1000000 ^ (2 * K + 1) * Q,
   6000000000000 * 2 ^ (2 * K - 1) * 6283184 ^ (2 * K + 1) * (2 * u) ^ (2 * K + 1) * N ^ (2 * K)
     * r * (4 * K + 1))

theorem remEven_sound (K N : ℕ) (hK1 : 1 ≤ K) (hK6 : K ≤ 6) (hN : 1 ≤ N) (u tn : ℕ) (hu : 0 < u)
    (t : ℝ) (ht : t = (tn : ℝ) / u) (Q r : ℕ) (hok : (remEven K u tn N Q r).1 = true) :
    ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖
      ≤ ((remEven K u tn N Q r).2.1 : ℝ) / ((remEven K u tn N Q r).2.2 : ℝ) := by
  simp only [remEven, Bool.and_eq_true, Nat.ble_eq] at hok ⊢
  obtain ⟨⟨hr1, hrN⟩, hQ⟩ := hok
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  set Qr : ℝ := (Q : ℝ) / (2 * u) ^ (2 * K) with hQr
  have hQr0 : 0 ≤ Qr := by positivity
  have hpn := pochNormSq_eq_pnK u tn hu t ht (2 * K)
  have hQsq : pochNormSq (1 / 2) t (2 * K) ≤ Qr ^ 2 := by
    rw [hpn, hQr, div_pow, ← pow_mul]
    have h2 : (0 : ℝ) < (2 * (u : ℝ)) ^ (2 * K * 2) := by positivity
    rw [show 2 * (2 * K) = 2 * K * 2 by ring]
    apply div_le_div_of_nonneg_right _ h2.le
    have : (pnK u tn (2 * K) : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast hQ
    push_cast at this; nlinarith [this]
  have hrem := em_line_remainder_le K hK1 t (N := N) hN Qr hQr0 hQsq r hr1
    (by rw [pow_two]; exact hrN)
  have hsOf : sOf t = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := rfl
  rw [hsOf]
  refine le_trans hrem (le_of_eq ?_)
  have hbeta := betaN_spec (2 * K - 2) (by omega)
  rw [show 2 * K - 2 + 2 = 2 * K by omega] at hbeta
  have hF : (0 : ℝ) < ((2 * K)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hL : (0 : ℝ) < (Lbeta : ℝ) := by norm_num [Lbeta]
  have habs : |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ)
      = (((betaN (2 * K - 2)).natAbs : ℤ) : ℝ) / (Lbeta : ℝ) := by
    rw [← abs_of_pos hF, ← abs_div, hbeta, abs_div, abs_of_pos hL, Int.natCast_natAbs, Int.cast_abs]
  rw [habs, hQr]
  have hK2 : ((2 * K : ℕ) : ℝ) - 1 / 2 = (4 * (K : ℝ) - 1) / 2 := by push_cast; ring
  rw [hK2]
  push_cast
  have hK4 : (0 : ℝ) < 4 * (K : ℝ) - 1 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith
  have h2u : (0 : ℝ) < (2 * (u : ℝ)) ^ (2 * K) := by positivity
  have hNp : (0 : ℝ) < (N : ℝ) ^ (2 * K - 1) := by positivity
  field_simp

theorem remOdd_sound (K N : ℕ) (hK1 : 1 ≤ K) (hN : 1 ≤ N) (u tn : ℕ) (hu : 0 < u)
    (t : ℝ) (ht : t = (tn : ℝ) / u) (Q r : ℕ) (hok : (remOdd K u tn N Q r).1 = true) :
    ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖
      ≤ ((remOdd K u tn N Q r).2.1 : ℝ) / ((remOdd K u tn N Q r).2.2 : ℝ) := by
  simp only [remOdd, Bool.and_eq_true, Nat.ble_eq] at hok ⊢
  obtain ⟨⟨hr1, hrN⟩, hQ⟩ := hok
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  set Qr : ℝ := (Q : ℝ) / (2 * u) ^ (2 * K + 1) with hQr
  have hQr0 : 0 ≤ Qr := by positivity
  have hpn := pochNormSq_eq_pnK u tn hu t ht (2 * K + 1)
  have hQsq : pochNormSq (1 / 2) t (2 * K + 1) ≤ Qr ^ 2 := by
    rw [hpn, hQr, div_pow, ← pow_mul]
    have h2 : (0 : ℝ) < (2 * (u : ℝ)) ^ ((2 * K + 1) * 2) := by positivity
    rw [show 2 * (2 * K + 1) = (2 * K + 1) * 2 by ring]
    apply div_le_div_of_nonneg_right _ h2.le
    have : (pnK u tn (2 * K + 1) : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast hQ
    push_cast at this; nlinarith [this]
  have hrem := em_line_remainder_odd_le K hK1 t (N := N) hN Qr hQr0 hQsq r hr1
    (by rw [pow_two]; exact hrN)
  have hsOf : sOf t = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := rfl
  rw [hsOf]
  refine le_trans hrem ?_
  -- replace π by the rational brackets 6283184/10^6 < 2π, π < 3141593/10^6
  have hlo : (6283184 : ℝ) / 1000000 ≤ 2 * π := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hhi : π ≤ (3141593 : ℝ) / 1000000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hpipos : (0 : ℝ) < π := Real.pi_pos
  have hK2 : ((2 * K + 1 : ℕ) : ℝ) - 1 / 2 = (4 * (K : ℝ) + 1) / 2 := by push_cast; ring
  rw [hK2]
  have h4K : (0 : ℝ) < 4 * (K : ℝ) + 1 := by positivity
  have hden0 : (0 : ℝ) < (N : ℝ) ^ (2 * K) * r := by positivity
  have h2k : (0 : ℝ) < (2 : ℝ) ^ (2 * K - 1) := by positivity
  have hpi2 : π ^ 2 ≤ ((3141593 : ℝ) / 1000000) ^ 2 := by
    exact pow_le_pow_left₀ hpipos.le hhi 2
  have hnum0 : 0 ≤ 1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1) := by
    have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
    positivity
  calc 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * Qr
        / ((N : ℝ) ^ (2 * K) * r) / ((4 * (K : ℝ) + 1) / 2)
      ≤ 2 * (1 + (((3141593 : ℝ) / 1000000) ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          / ((6283184 : ℝ) ^ (2 * K + 1) / 1000000 ^ (2 * K + 1)) * Qr
          / ((N : ℝ) ^ (2 * K) * r) / ((4 * (K : ℝ) + 1) / 2) := by
        rw [← div_pow]
        gcongr
    _ = _ := by
        rw [hQr]
        push_cast
        field_simp
        ring

/-! ## F. The checker and its soundness. -/

/-- The final-inequality core: given ANY remainder bound `EN/ED`, checks `1 ≤ K ≤ 6`, `N ≥ 2`,
    `0 < D`, `0 < ED` and the four final inequalities, multiplied through by `D · BD · ED`. -/
def checkCore (c : Cfg) (K N : ℕ) (s1 s2 : St) (D : ℕ) (reLo reHi imLo imHi EN ED : ℤ) : Bool :=
  let u := 2 ^ c.tq
  let cd := corrData K u c.tn N
  let BreN := cd.1
  let BimN := cd.2.1
  let BD := cd.2.2
  let two : ℤ := 2 ^ c.P
  let a1 : ℤ := (s1.reP : ℤ) - s1.reN
  let b1 : ℤ := (s1.imP : ℤ) - s1.imN
  let za : ℤ := ((s2.reP : ℤ) - s2.reN) - a1
  let zb : ℤ := ((s2.imP : ℤ) - s2.imN) - b1
  let zra : ℤ := (s2.reR : ℤ) + s1.reR
  let zrb : ℤ := (s2.imR : ℤ) + s1.imR
  let aB : ℤ := BreN.natAbs
  let aC : ℤ := BimN.natAbs
  let CreN := a1 * BD + za * BreN - zb * BimN
  let RreN := (s1.reR : ℤ) * BD + zra * aB + zrb * aC
  let CimN := b1 * BD + za * BimN + zb * BreN
  let RimN := (s1.imR : ℤ) * BD + zra * aC + zrb * aB
  let DD : ℤ := D
  Nat.ble 1 K && Nat.ble K 6 && Nat.ble 2 N && Nat.ble 1 D && decide (0 < ED) &&
    decide (reLo * two * BD * ED ≤ DD * ED * (CreN - RreN) - DD * BD * EN * two) &&
    decide (DD * ED * (CreN + RreN) + DD * BD * EN * two ≤ reHi * two * BD * ED) &&
    decide (imLo * two * BD * ED ≤ DD * ED * (CimN - RimN) - DD * BD * EN * two) &&
    decide (DD * ED * (CimN + RimN) + DD * BD * EN * two ≤ imHi * two * BD * ED)

/-- **The kernel checker.**  `odd = false`: even-saw remainder (`Q² ≥ pnK(2K)`); `odd = true`:
    odd-saw remainder (`Q² ≥ pnK(2K+1)`, about 7 percent fewer terms at the same width). -/
def checkK (c : Cfg) (K N : ℕ) (s1 s2 : St) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Q r : ℕ)
    (odd : Bool) : Bool :=
  let R := cond odd (remOdd K (2 ^ c.tq) c.tn N Q r) (remEven K (2 ^ c.tq) c.tn N Q r)
  R.1 && checkCore c K N s1 s2 D reLo reHi imLo imHi R.2.1 R.2.2

/-- Dividing an integer inequality by a positive real factor. -/
theorem real_le_of_int_le {X Y c : ℝ} (hc : 0 < c) {A B : ℤ} (hA : (A : ℝ) = X * c)
    (hB : (B : ℝ) = Y * c) (h : A ≤ B) : X ≤ Y := by
  have h' : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast h
  rw [hA, hB] at h'
  exact le_of_mul_le_mul_right h' hc

/-- **Soundness of the final-inequality core**, for any remainder bound `EN/ED`. -/
theorem checkCore_sound (c : Cfg) (t : ℝ) (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N : ℕ) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (D : ℕ) (reLo reHi imLo imHi EN ED : ℤ)
    (hE : ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖ ≤ (EN : ℝ) / (ED : ℝ))
    (hc : checkCore c K N s1 s2 D reLo reHi imLo imHi EN ED = true) :
    ((reLo : ℝ) / D ≤ (riemannZeta (sOf t)).re ∧ (riemannZeta (sOf t)).re ≤ (reHi : ℝ) / D) ∧
    ((imLo : ℝ) / D ≤ (riemannZeta (sOf t)).im ∧ (riemannZeta (sOf t)).im ≤ (imHi : ℝ) / D) := by
  simp only [checkCore, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, hD1⟩, hEDpos⟩, hreLo⟩, hreHi⟩, himLo⟩, himHi⟩ := hc
  set u : ℕ := 2 ^ c.tq with hudef
  have hu : 0 < u := Nat.two_pow_pos _
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have ht' : t = (c.tn : ℝ) / u := by rw [ht, hudef]; push_cast; ring
  obtain ⟨hcre, hcim⟩ := corr_eq K u c.tn N hK1 hK6 hu (by omega) t ht'
  set cd := corrData K u c.tn N with hcd
  set BreN := cd.1 with hBreN
  set BimN := cd.2.1 with hBimN
  set BD := cd.2.2 with hBD
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBDpos : (0 : ℝ) < (BD : ℝ) := by
    have e : (BD : ℝ) = 2 * ((u : ℝ) * u + (2 * c.tn) * (2 * c.tn))
        * ((Lbeta : ℝ) * (2 * u * N) ^ (2 * K - 1)) := by
      simp only [hBD, hcd, corrData]; push_cast; ring
    rw [e]
    have hL : (0 : ℝ) < (Lbeta : ℝ) := by norm_num [Lbeta]
    positivity
  have hEDR : (0 : ℝ) < (ED : ℝ) := by exact_mod_cast hEDpos
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD1
  have hP : (0 : ℝ) < (2 : ℝ) ^ c.P := by positivity
  have haRe : |(BreN : ℝ) / BD| ≤ ((BreN.natAbs : ℤ) : ℝ) / BD := by
    rw [abs_div, abs_of_pos hBDpos, Int.natCast_natAbs, Int.cast_abs]
  have haIm : |(BimN : ℝ) / BD| ≤ ((BimN.natAbs : ℤ) : ℝ) / BD := by
    rw [abs_div, abs_of_pos hBDpos, Int.natCast_natAbs, Int.cast_abs]
  have hc3 : (0 : ℝ) < (D : ℝ) * BD * ED := by positivity
  have hre := ArbEcon.OrderK.zetaK_re_bounds c K t N hN2 s1 s2 h1 h2 _ hE _ _ hcre hcim
    _ _ ((reLo : ℝ) / D) ((reHi : ℝ) / D) haRe haIm
    (real_le_of_int_le hc3 (by push_cast; field_simp) (by push_cast; field_simp; ring) hreLo)
    (real_le_of_int_le hc3 (by push_cast; field_simp; ring) (by push_cast; field_simp) hreHi)
  have him := ArbEcon.OrderK.zetaK_im_bounds c K t N hN2 s1 s2 h1 h2 _ hE _ _ hcre hcim
    _ _ ((imLo : ℝ) / D) ((imHi : ℝ) / D) haRe haIm
    (real_le_of_int_le hc3 (by push_cast; field_simp) (by push_cast; field_simp; ring) himLo)
    (real_le_of_int_le hc3 (by push_cast; field_simp; ring) (by push_cast; field_simp) himHi)
  exact ⟨hre, him⟩

/-- **Soundness of the kernel checker.**  If `checkK c K N s1 s2 D reLo reHi imLo imHi Q r odd = true`
    and `s1`, `s2` are evaluator invariants after `N - 1` and `N` terms at height
    `t = c.tn / 2^c.tq`, then `reLo/D ≤ Re ζ(1/2 + i t) ≤ reHi/D` and `imLo/D ≤ Im ζ(1/2 + i t) ≤ imHi/D`.
    The order-(2K+1) finite part and its remainder are `EMZetaHigh.em_line_remainder_le` (even saw)
    or `EMZetaHigh.em_line_remainder_odd_le` (odd saw). -/
theorem checkK_sound (c : Cfg) (t : ℝ) (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N : ℕ) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Q r : ℕ)
    (odd : Bool) (hc : checkK c K N s1 s2 D reLo reHi imLo imHi Q r odd = true) :
    ((reLo : ℝ) / D ≤ (riemannZeta (sOf t)).re ∧ (riemannZeta (sOf t)).re ≤ (reHi : ℝ) / D) ∧
    ((imLo : ℝ) / D ≤ (riemannZeta (sOf t)).im ∧ (riemannZeta (sOf t)).im ≤ (imHi : ℝ) / D) := by
  have hu : 0 < 2 ^ c.tq := Nat.two_pow_pos _
  have ht' : t = (c.tn : ℝ) / ((2 ^ c.tq : ℕ) : ℝ) := by rw [ht]; push_cast; ring
  simp only [checkK, Bool.and_eq_true] at hc
  obtain ⟨hR, hcore⟩ := hc
  -- the core fixes 1 ≤ K ≤ 6 and N ≥ 2
  have hcore' := hcore
  simp only [checkCore, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hcore'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcore'
  cases odd with
  | false =>
    exact checkCore_sound c t ht K N s1 s2 h1 h2 D reLo reHi imLo imHi _ _
      (remEven_sound K N hK1 hK6 (by omega) (2 ^ c.tq) c.tn hu t ht' Q r hR) hcore
  | true =>
    exact checkCore_sound c t ht K N s1 s2 h1 h2 D reLo reHi imLo imHi _ _
      (remOdd_sound K N hK1 (by omega) (2 ^ c.tq) c.tn hu t ht' Q r hR) hcore

end OrderK

end ArbEcon
