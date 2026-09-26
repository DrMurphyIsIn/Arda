/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
-/
import EMZetaOfflineSound
import EMZetaOfflineCore
import EMZetaHighCheck

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

open ArbEcon.OrderK (betaN Lbeta betaN_spec real_le_of_int_le)

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/

/-- `G_k = (q u)^k (σ + i t)_k`, `G_{k+1} = G_k · ((sN + k q) u + i tn q)`. -/
def gpochG (sN : ℤ) (q u tn : ℕ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 =>
    match gpochG sN q u tn k with
    | (x, y) => (x * ((sN + k * q) * u) - y * (tn * q), x * (tn * q) + y * ((sN + k * q) * u))

theorem gpochG_succ (sN : ℤ) (q u tn k : ℕ) :
    gpochG sN q u tn (k + 1) =
      ((gpochG sN q u tn k).1 * ((sN + k * q) * u) - (gpochG sN q u tn k).2 * (tn * q),
       (gpochG sN q u tn k).1 * (tn * q) + (gpochG sN q u tn k).2 * ((sN + k * q) * u)) := by
  show (match gpochG sN q u tn k with
    | (x, y) => (x * ((sN + k * q) * u) - y * (tn * q), x * (tn * q) + y * ((sN + k * q) * u))) = _
  rcases gpochG sN q u tn k with ⟨x, y⟩
  rfl

theorem pochRI_eq_gpochG (sN : ℤ) (q u tn : ℕ) (hq : 0 < q) (hu : 0 < u) (σ t : ℝ)
    (hσ : σ = (sN : ℝ) / q) (ht : t = (tn : ℝ) / u) (k : ℕ) :
    (pochRI σ t k).1 = ((gpochG sN q u tn k).1 : ℝ) / ((q : ℝ) * u) ^ k ∧
    (pochRI σ t k).2 = ((gpochG sN q u tn k).2 : ℝ) / ((q : ℝ) * u) ^ k := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  induction k with
  | zero => simp [pochRI, gpochG]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [gpochG_succ]
    simp only [pochRI]
    rw [h1, h2, hσ, ht]
    push_cast
    have hne : ((q : ℝ) * u) ^ k ≠ 0 := by positivity
    constructor <;> field_simp <;> ring

/-- `Σ_{i<j} βN_i · G_{i+1} · W^(M-1-i)`. -/
def gsumG (sN : ℤ) (q u tn : ℕ) (W : ℤ) (M : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | j + 1 => ((gsumG sN q u tn W M j).1 + betaN j * (gpochG sN q u tn (j + 1)).1 * W ^ (M - 1 - j),
              (gsumG sN q u tn W M j).2 + betaN j * (gpochG sN q u tn (j + 1)).2 * W ^ (M - 1 - j))

theorem gsumG_eq (sN : ℤ) (q u tn : ℕ) (W : ℤ) (M j : ℕ) :
    ((gsumG sN q u tn W M j).1 : ℝ)
        = ∑ i ∈ Finset.range j, (betaN i : ℝ) * ((gpochG sN q u tn (i + 1)).1 : ℝ) * (W : ℝ) ^ (M - 1 - i) ∧
    ((gsumG sN q u tn W M j).2 : ℝ)
        = ∑ i ∈ Finset.range j, (betaN i : ℝ) * ((gpochG sN q u tn (i + 1)).2 : ℝ) * (W : ℝ) ^ (M - 1 - i) := by
  induction j with
  | zero => simp [gsumG]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [gsumG, Finset.sum_range_succ]
    push_cast
    rw [h1, h2]
    exact ⟨rfl, rfl⟩

/-- The exact correction factor `emCorr K (σ + i t) N = (BreN + i BimN) / BD`, `σ = sN/q`,
    `t = tn/u`: returns `(BreN, BimN, BD)`. -/
def corrDataG (K : ℕ) (sN : ℤ) (q u tn N : ℕ) : ℤ × ℤ × ℤ :=
  let M := 2 * K - 1
  let W : ℤ := (q : ℤ) * u * N
  let q2 : ℤ := (sN - q) ^ 2 * (u : ℤ) ^ 2 + (tn : ℤ) ^ 2 * (q : ℤ) ^ 2
  let base : ℤ := Lbeta * W ^ M
  let S := gsumG sN q u tn W M M
  (2 * N * q * (u : ℤ) ^ 2 * (sN - q) * base + q2 * base + 2 * q2 * S.1,
   -(2 * N * (q : ℤ) ^ 2 * u * tn * base) + 2 * q2 * S.2,
   2 * q2 * base)

theorem corr_eqG (K : ℕ) (sN : ℤ) (q u tn N : ℕ) (hK1 : 1 ≤ K) (hK6 : K ≤ 6) (hq : 0 < q)
    (hu : 0 < u) (htn : 0 < tn) (hN : 1 ≤ N) (σ t : ℝ) (hσ : σ = (sN : ℝ) / q)
    (ht : t = (tn : ℝ) / u) :
    emCorrRe K σ t N = ((corrDataG K sN q u tn N).1 : ℝ) / ((corrDataG K sN q u tn N).2.2 : ℝ) ∧
    emCorrIm K σ t N = ((corrDataG K sN q u tn N).2.1 : ℝ) / ((corrDataG K sN q u tn N).2.2 : ℝ) := by
  set M := 2 * K - 1 with hM
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have htnR : (0 : ℝ) < tn := by exact_mod_cast htn
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hWR : (0 : ℝ) < (q : ℝ) * u * N := by positivity
  have hq2 : (0 : ℝ) < ((sN : ℝ) - q) ^ 2 * (u : ℝ) ^ 2 + (tn : ℝ) ^ 2 * (q : ℝ) ^ 2 := by positivity
  have hL : (0 : ℝ) < (Lbeta : ℝ) := by norm_num [Lbeta]
  obtain ⟨hS1, hS2⟩ := gsumG_eq sN q u tn ((q : ℤ) * u * N) M M
  have key : ∀ (sel : ℕ → ℤ) (p : ℕ → ℝ),
      (∀ i, i < M → p (i + 1) = (sel (i + 1) : ℝ) / ((q : ℝ) * u) ^ (i + 1)) →
      (∑ i ∈ Finset.range M,
          (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * p (i + 1))
        = (∑ i ∈ Finset.range M, (betaN i : ℝ) * (sel (i + 1) : ℝ)
            * ((((q : ℤ) * u * N : ℤ)) : ℝ) ^ (M - 1 - i))
            / ((Lbeta : ℝ) * ((((q : ℤ) * u * N : ℤ)) : ℝ) ^ M) := by
    intro sel p hp
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hiM : i < M := Finset.mem_range.mp hi
    have hi10 : i ≤ 10 := by omega
    rw [betaN_spec i hi10, hp i hiM]
    push_cast
    have hpow : ((q : ℝ) * u * N) ^ M = ((q : ℝ) * u * N) ^ (M - 1 - i) * ((q : ℝ) * u * N) ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    have h1 : ((q : ℝ) * u * N) ^ (M - 1 - i) ≠ 0 := by positivity
    have h2 : ((q : ℝ) * u) ^ (i + 1) ≠ 0 := by positivity
    have h3 : (N : ℝ) ^ (i + 1) ≠ 0 := by positivity
    rw [mul_pow ((q : ℝ) * u) (N : ℝ)]
    field_simp
    ring
  have hpR := fun i (_ : i < M) => (pochRI_eq_gpochG sN q u tn hq hu σ t hσ ht (i + 1)).1
  have hpI := fun i (_ : i < M) => (pochRI_eq_gpochG sN q u tn hq hu σ t hσ ht (i + 1)).2
  have kR := key (fun k => (gpochG sN q u tn k).1) (fun k => (pochRI σ t k).1) hpR
  have kI := key (fun k => (gpochG sN q u tn k).2) (fun k => (pochRI σ t k).2) hpI
  constructor
  · simp only [emCorrRe]
    rw [← hM, kR]
    simp only [corrDataG]
    rw [← hM]
    push_cast at hS1 ⊢
    rw [← hS1]
    subst hσ ht
    field_simp
  · simp only [emCorrIm]
    rw [← hM, kI]
    simp only [corrDataG]
    rw [← hM]
    push_cast at hS2 ⊢
    rw [← hS2]
    subst hσ ht
    field_simp

/-! ## B. The remainder numerator and `N^(-σ)`. -/

/-- `Π_{j<k} ((sN + j q)² u² + tn² q²)` (the `(q u)^(2k)`-scaled `‖(σ + i t)_k‖²`). -/
def pnG (sN : ℤ) (q u tn : ℕ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => pnG sN q u tn k * ((sN + k * q) ^ 2 * (u : ℤ) ^ 2 + (tn : ℤ) ^ 2 * (q : ℤ) ^ 2)

theorem pochNormSq_eq_pnG (sN : ℤ) (q u tn : ℕ) (hq : 0 < q) (hu : 0 < u) (σ t : ℝ)
    (hσ : σ = (sN : ℝ) / q) (ht : t = (tn : ℝ) / u) (k : ℕ) :
    pochNormSq σ t k = (pnG sN q u tn k : ℝ) / ((q : ℝ) * u) ^ (2 * k) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  induction k with
  | zero => simp [pochNormSq, pnG]
  | succ k ih =>
    rw [pochNormSq, ih, pnG]
    push_cast
    subst hσ ht
    have hne : ((q : ℝ) * u) ^ (2 * k) ≠ 0 := by positivity
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    field_simp

/-- `N^(-σ) ≤ Rn / Rd` for `σ = (a - b)/q` from the integer certificate `Rd^q N^b ≤ Rn^q N^a`. -/
theorem rpow_neg_le_of_pow (N : ℕ) (hN : 1 ≤ N) (a b q : ℕ) (hq : 1 ≤ q) (Rn Rd : ℕ)
    (hRd : 0 < Rd) (h : Rd ^ q * N ^ b ≤ Rn ^ q * N ^ a) :
    (N : ℝ) ^ (-(((a : ℝ) - b) / q)) ≤ (Rn : ℝ) / Rd := by
  set X := (N : ℝ) ^ (-(((a : ℝ) - b) / q)) with hX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hX0 : 0 ≤ X := by positivity
  have hRdR : (0 : ℝ) < Rd := by exact_mod_cast hRd
  have hNa : (0 : ℝ) < (N : ℝ) ^ a := by positivity
  have hid := rpow_neg_sigma_pow N hN a b q hq
  rw [← hX] at hid
  have hR : (Rd : ℝ) ^ q * (N : ℝ) ^ b ≤ (Rn : ℝ) ^ q * (N : ℝ) ^ a := by exact_mod_cast h
  have hXq : X ^ q ≤ ((Rn : ℝ) / Rd) ^ q := by
    rw [div_pow]
    have hRdq : (0 : ℝ) < (Rd : ℝ) ^ q := by positivity
    rw [le_div_iff₀ hRdq]
    have : X ^ q * (N : ℝ) ^ a * (Rd : ℝ) ^ q ≤ (Rn : ℝ) ^ q * (N : ℝ) ^ a := by
      rw [hid]; linarith
    nlinarith
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hXq

/-! ## C. The odd-saw remainder certificate, off the line. -/

/-- `(ok, EN, ED)`: `ok` checks `1 ≤ Rd`, `1 ≤ K`, `pnG(2K+1) ≤ Qp²`, `Rd^q N^b ≤ Rn^q N^a`,
    `0 < sN + 2Kq`; then `‖ζ(s) − emFinite K s N‖ ≤ EN/ED` (with `6.283184 < 2π`, `π < 3.141593`). -/
def remOddG (K a b q u tn N Qp Rn Rd : ℕ) : Bool × ℤ × ℤ :=
  let sN : ℤ := (a : ℤ) - b
  (Nat.ble 1 Rd && Nat.ble 1 K && decide (pnG sN q u tn (2 * K + 1) ≤ (Qp : ℤ) * Qp) &&
     Nat.ble (Rd ^ q * N ^ b) (Rn ^ q * N ^ a) && decide (0 < sN + 2 * K * q),
   2 * (6000000000000 * 2 ^ (2 * K - 1) + 9869606577649 - 6000000000000) * 1000000 ^ (2 * K + 1)
     * Qp * Rn * q,
   6000000000000 * 2 ^ (2 * K - 1) * 6283184 ^ (2 * K + 1) * ((q : ℤ) * u) ^ (2 * K + 1) * Rd
     * (N : ℤ) ^ (2 * K) * (sN + 2 * K * q))

theorem remOddG_sound (K N : ℕ) (hN : 1 ≤ N) (a b q u tn : ℕ) (hq : 0 < q) (hu : 0 < u)
    (htn : 0 < tn) (σ t : ℝ) (hσ : σ = ((a : ℝ) - b) / q) (ht : t = (tn : ℝ) / u) (Qp Rn Rd : ℕ)
    (hok : (remOddG K a b q u tn N Qp Rn Rd).1 = true) :
    ‖riemannZeta (sOfG σ t) - emFinite K (sOfG σ t) N‖
      ≤ ((remOddG K a b q u tn N Qp Rn Rd).2.1 : ℝ) / ((remOddG K a b q u tn N Qp Rn Rd).2.2 : ℝ) := by
  simp only [remOddG, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨⟨⟨hRd, hK⟩, hQ⟩, hR⟩, hpos⟩ := hok
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have htR : 0 < t := by rw [ht]; exact div_pos (by exact_mod_cast htn) huR
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRdR : (0 : ℝ) < Rd := by exact_mod_cast hRd
  set sN : ℤ := (a : ℤ) - b with hsN
  have hσ' : σ = (sN : ℝ) / q := by rw [hσ, hsN]; push_cast; ring
  have hposR : (0 : ℝ) < (sN : ℝ) + 2 * K * q := by exact_mod_cast hpos
  have hσK : 0 < σ + 2 * K := by
    rw [hσ']
    have : (sN : ℝ) / q + 2 * K = ((sN : ℝ) + 2 * K * q) / q := by field_simp
    rw [this]; positivity
  -- the analytic bound
  have hs1 : sOfG σ t ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [sOfG] at this
    linarith
  have hsre : (sOfG σ t).re = σ := by simp [sOfG]
  have henc := EMOff.em_zeta_orderK_enclosure_odd_ext K hK (s := sOfG σ t)
    (by rw [hsre]; push_cast; linarith) hs1 hN
  rw [hsre] at henc
  -- the Pochhammer factor
  set Qr : ℝ := (Qp : ℝ) / ((q : ℝ) * u) ^ (2 * K + 1) with hQr
  have hQr0 : 0 ≤ Qr := by positivity
  have hpn := pochNormSq_eq_pnG sN q u tn hq hu σ t hσ' ht (2 * K + 1)
  have hQsq : pochNormSq σ t (2 * K + 1) ≤ Qr ^ 2 := by
    rw [hpn, hQr, div_pow, ← pow_mul]
    have h2 : (0 : ℝ) < ((q : ℝ) * u) ^ ((2 * K + 1) * 2) := by positivity
    rw [show 2 * (2 * K + 1) = (2 * K + 1) * 2 by ring]
    apply div_le_div_of_nonneg_right _ h2.le
    have : (pnG sN q u tn (2 * K + 1) : ℝ) ≤ ((Qp : ℤ) * Qp : ℤ) := by exact_mod_cast hQ
    push_cast at this; nlinarith [this]
  have hpoch : ‖poch (sOfG σ t) (2 * K + 1)‖ ≤ Qr := norm_poch_le σ t (2 * K + 1) Qr hQr0 hQsq
  -- the power of N
  have hNσ : (N : ℝ) ^ (-σ) ≤ (Rn : ℝ) / Rd := by
    rw [hσ]; exact rpow_neg_le_of_pow N hN a b q hq Rn Rd hRd (by exact_mod_cast hR)
  have hpowN : (N : ℝ) ^ (-(σ + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤ (Rn : ℝ) / Rd / (N : ℝ) ^ (2 * K) := by
    have e : -(σ + ((2 * K + 1 : ℕ) : ℝ) - 1) = -σ + (-(((2 * K : ℕ) : ℝ))) := by push_cast; ring
    have hk : (N : ℝ) ^ (-(((2 * K : ℕ) : ℝ))) = ((N : ℝ) ^ (2 * K))⁻¹ := by
      rw [Real.rpow_neg hNR.le, Real.rpow_natCast]
    rw [e, Real.rpow_add hNR, hk, div_eq_mul_inv ((Rn : ℝ) / Rd)]
    exact mul_le_mul_of_nonneg_right hNσ (by positivity)
  have hden : σ + ((2 * K + 1 : ℕ) : ℝ) - 1 = ((sN : ℝ) + 2 * K * q) / q := by
    rw [hσ']; push_cast; field_simp; ring
  -- the constant
  have hlo : (6283184 : ℝ) / 1000000 ≤ 2 * π := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hhi : π ≤ (3141593 : ℝ) / 1000000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hpipos : (0 : ℝ) < π := Real.pi_pos
  have hpi2 : π ^ 2 ≤ ((3141593 : ℝ) / 1000000) ^ 2 := pow_le_pow_left₀ hpipos.le hhi 2
  have hC : 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1)
      ≤ 2 * (1 + ((3141593 : ℝ) ^ 2 / 1000000 ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          / ((6283184 : ℝ) ^ (2 * K + 1) / 1000000 ^ (2 * K + 1)) := by
    have h2k : (0 : ℝ) < (2 : ℝ) ^ (2 * K - 1) := by positivity
    have hnum0 : 0 ≤ 1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1) := by
      have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
      positivity
    rw [← div_pow, ← div_pow]
    gcongr
  have hC0 : 0 ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) := by
    have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
    positivity
  refine le_trans henc ?_
  rw [hden]
  have hdpos : (0 : ℝ) < ((sN : ℝ) + 2 * K * q) / q := by positivity
  have hpowN' : (N : ℝ) ^ (-(((sN : ℝ) + 2 * K * q) / q)) ≤ (Rn : ℝ) / Rd / (N : ℝ) ^ (2 * K) := by
    rw [← hden]; exact hpowN
  have hne1 : (sN : ℝ) + 2 * K * q ≠ 0 := hposR.ne'
  have hne2 : ((q : ℝ) * u) ^ (2 * K + 1) ≠ 0 := by positivity
  have hne3 : (N : ℝ) ^ (2 * K) ≠ 0 := by positivity
  have hne4 : (2 : ℝ) ^ (2 * K - 1) ≠ 0 := by positivity
  have hne5 : (Rd : ℝ) ≠ 0 := hRdR.ne'
  have hne6 : (q : ℝ) ≠ 0 := hqR.ne'
  calc _ ≤ 2 * (1 + ((3141593 : ℝ) ^ 2 / 1000000 ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          / ((6283184 : ℝ) ^ (2 * K + 1) / 1000000 ^ (2 * K + 1)) * Qr
          * ((Rn : ℝ) / Rd / (N : ℝ) ^ (2 * K)) / (((sN : ℝ) + 2 * K * q) / q) := by
        gcongr
    _ = _ := by
        rw [hQr]
        push_cast
        field_simp
        ring

/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/

theorem psumK_zero_eq (σ t : ℝ) (n : ℕ) :
    psumK σ t 0 n = ∑ m ∈ Finset.Ico 1 (n + 1), (m : ℂ) ^ (-sOfG σ t) := by
  simp [psumK]

theorem emFinite_split (K : ℕ) (σ t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    emFinite K (sOfG σ t) N
      = psumK σ t 0 (N - 1) + (N : ℂ) ^ (-sOfG σ t) * emCorr K (sOfG σ t) N := by
  rw [psumK_zero_eq, show N - 1 + 1 = N by omega]
  rfl

theorem zeta_ballG (P : ℕ) (σ t : ℝ) (K N : ℕ) (hN : 2 ≤ N) (x1 x2 : Acc)
    (h1 : AccOK P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK P (psumK σ t 0 N) x2) (E : ℝ)
    (hE : ‖riemannZeta (sOfG σ t) - emFinite K (sOfG σ t) N‖ ≤ E) (Bre Bim : ℝ)
    (hBre : emCorrRe K σ t N = Bre) (hBim : emCorrIm K σ t N = Bim) :
    let a1 := (x1.reP : ℝ) - x1.reN
    let b1 := (x1.imP : ℝ) - x1.imN
    let za := ((x2.reP : ℝ) - x2.reN) - a1
    let zb := ((x2.imP : ℝ) - x2.imN) - b1
    let zra := (x2.reR : ℝ) + x1.reR
    let zrb := (x2.imR : ℝ) + x1.imR
    |(riemannZeta (sOfG σ t)).re * 2 ^ P - (a1 + za * Bre - zb * Bim)|
        ≤ x1.reR + zra * |Bre| + zrb * |Bim| + E * 2 ^ P ∧
    |(riemannZeta (sOfG σ t)).im * 2 ^ P - (b1 + za * Bim + zb * Bre)|
        ≤ x1.imR + zra * |Bim| + zrb * |Bre| + E * 2 ^ P := by
  intro a1 b1 za zb zra zrb
  obtain ⟨hre1, him1⟩ := h1
  obtain ⟨hre2, him2⟩ := h2
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hNm : N - 1 + 1 = N := by omega
  have hZ : (N : ℂ) ^ (-sOfG σ t) = psumK σ t 0 N - psumK σ t 0 (N - 1) := by
    have := psumK_succ σ t 0 (N - 1)
    rw [hNm] at this
    rw [this, pow_zero, one_mul]; ring
  have hZre : |((N : ℂ) ^ (-sOfG σ t)).re * 2 ^ P - za| ≤ zra := by
    rw [hZ, Complex.sub_re]
    have : ((psumK σ t 0 N).re - (psumK σ t 0 (N - 1)).re) * 2 ^ P - za
        = ((psumK σ t 0 N).re * 2 ^ P - ((x2.reP : ℝ) - x2.reN))
          - ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1) := by ring
    rw [this]; exact le_trans (abs_sub _ _) (add_le_add hre2 hre1)
  have hZim : |((N : ℂ) ^ (-sOfG σ t)).im * 2 ^ P - zb| ≤ zrb := by
    rw [hZ, Complex.sub_im]
    have : ((psumK σ t 0 N).im - (psumK σ t 0 (N - 1)).im) * 2 ^ P - zb
        = ((psumK σ t 0 N).im * 2 ^ P - ((x2.imP : ℝ) - x2.imN))
          - ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1) := by ring
    rw [this]; exact le_trans (abs_sub _ _) (add_le_add him2 him1)
  have hsplit := emFinite_split K σ t N (by omega)
  set B := emCorr K (sOfG σ t) N with hB
  have hBre' : B.re = Bre := by rw [← hBre]; exact (emCorr_re_im K σ t N).1
  have hBim' : B.im = Bim := by rw [← hBim]; exact (emCorr_re_im K σ t N).2
  set Z := (N : ℂ) ^ (-sOfG σ t)
  have hEre : |(riemannZeta (sOfG σ t)).re - (emFinite K (sOfG σ t) N).re| ≤ E := by
    rw [← Complex.sub_re]; exact le_trans (Complex.abs_re_le_norm _) hE
  have hEim : |(riemannZeta (sOfG σ t)).im - (emFinite K (sOfG σ t) N).im| ≤ E := by
    rw [← Complex.sub_im]; exact le_trans (Complex.abs_im_le_norm _) hE
  rw [hsplit] at hEre hEim
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, hBre', hBim']
    at hEre hEim
  constructor
  · have e : (riemannZeta (sOfG σ t)).re * 2 ^ P - (a1 + za * Bre - zb * Bim)
        = ((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re + (Z.re * Bre - Z.im * Bim))) * 2 ^ P
          + ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1)
          + (Z.re * 2 ^ P - za) * Bre - (Z.im * 2 ^ P - zb) * Bim := by ring
    rw [e]
    have t1 : |((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re + (Z.re * Bre - Z.im * Bim)))
        * 2 ^ P| ≤ E * 2 ^ P := by
      rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEre (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ P - za) * Bre| ≤ zra * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ P - zb) * Bim| ≤ zrb * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    have q1 := abs_add_le (((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ P + ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1))
      ((Z.re * 2 ^ P - za) * Bre)
    have q2 := abs_add_le (((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ P) ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1)
    have q3 := abs_sub (((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ P + ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1)
      + (Z.re * 2 ^ P - za) * Bre) ((Z.im * 2 ^ P - zb) * Bim)
    linarith
  · have e : (riemannZeta (sOfG σ t)).im * 2 ^ P - (b1 + za * Bim + zb * Bre)
        = ((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im + (Z.re * Bim + Z.im * Bre))) * 2 ^ P
          + ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1)
          + (Z.re * 2 ^ P - za) * Bim + (Z.im * 2 ^ P - zb) * Bre := by ring
    rw [e]
    have t1 : |((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im + (Z.re * Bim + Z.im * Bre)))
        * 2 ^ P| ≤ E * 2 ^ P := by
      rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEim (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ P - za) * Bim| ≤ zra * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ P - zb) * Bre| ≤ zrb * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    have q1 := abs_add_le (((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ P + ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1))
      ((Z.re * 2 ^ P - za) * Bim)
    have q2 := abs_add_le (((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ P) ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1)
    have q3 := abs_add_le (((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ P + ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1)
      + (Z.re * 2 ^ P - za) * Bim) ((Z.im * 2 ^ P - zb) * Bre)
    linarith

/-! ## E. The kernel checker and its soundness. -/

/-- The final-inequality core for ANY remainder bound `EN/ED` (multiplied through by `D·BD·ED`). -/
def checkCoreG (P tq tn K : ℕ) (sN : ℤ) (q N : ℕ) (x1 x2 : Acc) (D : ℕ)
    (reLo reHi imLo imHi EN ED : ℤ) : Bool :=
  let u := 2 ^ tq
  let cd := corrDataG K sN q u tn N
  let BreN := cd.1
  let BimN := cd.2.1
  let BD := cd.2.2
  let two : ℤ := 2 ^ P
  let a1 : ℤ := (x1.reP : ℤ) - x1.reN
  let b1 : ℤ := (x1.imP : ℤ) - x1.imN
  let za : ℤ := ((x2.reP : ℤ) - x2.reN) - a1
  let zb : ℤ := ((x2.imP : ℤ) - x2.imN) - b1
  let zra : ℤ := (x2.reR : ℤ) + x1.reR
  let zrb : ℤ := (x2.imR : ℤ) + x1.imR
  let aB : ℤ := BreN.natAbs
  let aC : ℤ := BimN.natAbs
  let CreN := a1 * BD + za * BreN - zb * BimN
  let RreN := (x1.reR : ℤ) * BD + zra * aB + zrb * aC
  let CimN := b1 * BD + za * BimN + zb * BreN
  let RimN := (x1.imR : ℤ) * BD + zra * aC + zrb * aB
  let DD : ℤ := D
  Nat.ble 1 K && Nat.ble K 6 && Nat.ble 2 N && Nat.ble 1 D && decide (0 < ED) && Nat.ble 1 q &&
    Nat.ble 1 tn &&
    decide (reLo * two * BD * ED ≤ DD * ED * (CreN - RreN) - DD * BD * EN * two) &&
    decide (DD * ED * (CreN + RreN) + DD * BD * EN * two ≤ reHi * two * BD * ED) &&
    decide (imLo * two * BD * ED ≤ DD * ED * (CimN - RimN) - DD * BD * EN * two) &&
    decide (DD * ED * (CimN + RimN) + DD * BD * EN * two ≤ imHi * two * BD * ED)

/-- **The off-line kernel checker**: the odd-saw remainder certificate `remOddG` and the core. -/
def checkG (c : Cfg) (o : OCfg) (K N : ℕ) (x1 x2 : Acc) (D : ℕ) (reLo reHi imLo imHi : ℤ)
    (Qp Rn Rd : ℕ) : Bool :=
  let R := remOddG K o.a o.b o.q (2 ^ c.tq) c.tn N Qp Rn Rd
  R.1 && checkCoreG c.P c.tq c.tn K ((o.a : ℤ) - o.b) o.q N x1 x2 D reLo reHi imLo imHi R.2.1 R.2.2

set_option maxHeartbeats 1000000 in
theorem checkCoreG_sound (P tq tn K : ℕ) (a b q N : ℕ) (σ t : ℝ) (hσ : σ = ((a : ℝ) - b) / q)
    (ht : t = (tn : ℝ) / 2 ^ tq) (x1 x2 : Acc)
    (h1 : AccOK P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK P (psumK σ t 0 N) x2) (D : ℕ)
    (reLo reHi imLo imHi EN ED : ℤ)
    (hE : ‖riemannZeta (sOfG σ t) - emFinite K (sOfG σ t) N‖ ≤ (EN : ℝ) / (ED : ℝ))
    (hc : checkCoreG P tq tn K ((a : ℤ) - b) q N x1 x2 D reLo reHi imLo imHi EN ED = true) :
    ((reLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).re ∧ (riemannZeta (sOfG σ t)).re ≤ (reHi : ℝ) / D) ∧
    ((imLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).im ∧ (riemannZeta (sOfG σ t)).im ≤ (imHi : ℝ) / D) := by
  simp only [checkCoreG, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, hD1⟩, hEDpos⟩, hq1⟩, htn1⟩, hreLo⟩, hreHi⟩, himLo⟩, himHi⟩ := hc
  set u : ℕ := 2 ^ tq with hudef
  have hu : 0 < u := Nat.two_pow_pos _
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have ht' : t = (tn : ℝ) / u := by rw [ht, hudef]; push_cast; ring
  have hσ' : σ = (((a : ℤ) - b : ℤ) : ℝ) / q := by rw [hσ]; push_cast; ring
  obtain ⟨hcre, hcim⟩ := corr_eqG K ((a : ℤ) - b) q u tn N hK1 hK6 (by omega) hu (by omega)
    (by omega) σ t hσ' ht'
  set cd := corrDataG K ((a : ℤ) - b) q u tn N with hcd
  set BreN := cd.1 with hBreN
  set BimN := cd.2.1 with hBimN
  set BD := cd.2.2 with hBD
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have htnR : (0 : ℝ) < tn := by exact_mod_cast (show 0 < tn by omega)
  have hBDpos : (0 : ℝ) < (BD : ℝ) := by
    have e : (BD : ℝ) = 2 * (((((a : ℤ) - b : ℤ) : ℝ) - q) ^ 2 * (u : ℝ) ^ 2 + (tn : ℝ) ^ 2 * (q : ℝ) ^ 2)
        * ((Lbeta : ℝ) * ((q : ℝ) * u * N) ^ (2 * K - 1)) := by
      simp only [hBD, hcd, corrDataG]; push_cast; ring
    rw [e]
    have hL : (0 : ℝ) < (Lbeta : ℝ) := by norm_num [Lbeta]
    positivity
  have hEDR : (0 : ℝ) < (ED : ℝ) := by exact_mod_cast hEDpos
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD1
  have hP : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have haRe : |(BreN : ℝ) / BD| ≤ ((BreN.natAbs : ℤ) : ℝ) / BD := by
    rw [abs_div, abs_of_pos hBDpos, Int.natCast_natAbs, Int.cast_abs]
  have haIm : |(BimN : ℝ) / BD| ≤ ((BimN.natAbs : ℤ) : ℝ) / BD := by
    rw [abs_div, abs_of_pos hBDpos, Int.natCast_natAbs, Int.cast_abs]
  have hball := zeta_ballG P σ t K N hN2 x1 x2 h1 h2 _ hE _ _ hcre hcim
  simp only at hball
  obtain ⟨hbre, hbim⟩ := hball
  have hBabs : |(BreN : ℝ) / BD| = |(BreN : ℝ)| / BD := by rw [abs_div, abs_of_pos hBDpos]
  have hCabs : |(BimN : ℝ) / BD| = |(BimN : ℝ)| / BD := by rw [abs_div, abs_of_pos hBDpos]
  rw [hBabs, hCabs] at hbre hbim
  rw [abs_le] at hbre hbim
  have hc3 : (0 : ℝ) < (D : ℝ) * BD * ED := by positivity
  have hk : (0 : ℝ) < 2 ^ P * BD * ED := by positivity
  have cast1 := (Int.cast_le (R := ℝ)).mpr hreLo
  have cast2 := (Int.cast_le (R := ℝ)).mpr hreHi
  have cast3 := (Int.cast_le (R := ℝ)).mpr himLo
  have cast4 := (Int.cast_le (R := ℝ)).mpr himHi
  push_cast at cast1 cast2 cast3 cast4
  have hBDne : (BD : ℝ) ≠ 0 := ne_of_gt hBDpos
  have hEDne : (ED : ℝ) ≠ 0 := ne_of_gt hEDR
  have id_re_lo : (D : ℝ) * ED * ((((x1.reP : ℝ) - x1.reN) * BD + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * BreN - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * BimN) - ((x1.reR : ℝ) * BD + ((x2.reR : ℝ) + x1.reR) * |(BreN : ℝ)| + ((x2.imR : ℝ) + x1.imR) * |(BimN : ℝ)|)) - D * BD * EN * 2 ^ P
      = (D * BD * ED) * ((((x1.reP : ℝ) - x1.reN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BreN : ℝ) / BD) - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BimN : ℝ) / BD)) - ((x1.reR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BreN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BimN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P))) := by
    field_simp; ring
  have id_re_hi : (D : ℝ) * ED * ((((x1.reP : ℝ) - x1.reN) * BD + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * BreN - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * BimN) + ((x1.reR : ℝ) * BD + ((x2.reR : ℝ) + x1.reR) * |(BreN : ℝ)| + ((x2.imR : ℝ) + x1.imR) * |(BimN : ℝ)|)) + D * BD * EN * 2 ^ P
      = (D * BD * ED) * ((((x1.reP : ℝ) - x1.reN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BreN : ℝ) / BD) - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BimN : ℝ) / BD)) + ((x1.reR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BreN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BimN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P))) := by
    field_simp; ring
  have id_im_lo : (D : ℝ) * ED * ((((x1.imP : ℝ) - x1.imN) * BD + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * BimN + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * BreN) - ((x1.imR : ℝ) * BD + ((x2.reR : ℝ) + x1.reR) * |(BimN : ℝ)| + ((x2.imR : ℝ) + x1.imR) * |(BreN : ℝ)|)) - D * BD * EN * 2 ^ P
      = (D * BD * ED) * ((((x1.imP : ℝ) - x1.imN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BimN : ℝ) / BD) + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BreN : ℝ) / BD)) - ((x1.imR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BimN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BreN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P))) := by
    field_simp; ring
  have id_im_hi : (D : ℝ) * ED * ((((x1.imP : ℝ) - x1.imN) * BD + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * BimN + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * BreN) + ((x1.imR : ℝ) * BD + ((x2.reR : ℝ) + x1.reR) * |(BimN : ℝ)| + ((x2.imR : ℝ) + x1.imR) * |(BreN : ℝ)|)) + D * BD * EN * 2 ^ P
      = (D * BD * ED) * ((((x1.imP : ℝ) - x1.imN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BimN : ℝ) / BD) + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BreN : ℝ) / BD)) + ((x1.imR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BimN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BreN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P))) := by
    field_simp; ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [div_le_iff₀ hDR]
    have hlow : (((x1.reP : ℝ) - x1.reN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BreN : ℝ) / BD) - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BimN : ℝ) / BD)) - ((x1.reR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BreN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BimN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P)) ≤ (riemannZeta (sOfG σ t)).re * 2 ^ P := by linarith [hbre.1]
    have hm := mul_le_mul_of_nonneg_left hlow hc3.le
    have : (reLo : ℝ) * (2 ^ P * BD * ED) ≤ (riemannZeta (sOfG σ t)).re * D * (2 ^ P * BD * ED) := by
      linarith [cast1, id_re_lo, hm]
    exact le_of_mul_le_mul_right this hk
  · rw [le_div_iff₀ hDR]
    have hup : (riemannZeta (sOfG σ t)).re * 2 ^ P ≤ (((x1.reP : ℝ) - x1.reN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BreN : ℝ) / BD) - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BimN : ℝ) / BD)) + ((x1.reR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BreN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BimN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P)) := by linarith [hbre.2]
    have hm := mul_le_mul_of_nonneg_left hup hc3.le
    have : (riemannZeta (sOfG σ t)).re * D * (2 ^ P * BD * ED) ≤ (reHi : ℝ) * (2 ^ P * BD * ED) := by
      linarith [cast2, id_re_hi, hm]
    exact le_of_mul_le_mul_right this hk
  · rw [div_le_iff₀ hDR]
    have hlow : (((x1.imP : ℝ) - x1.imN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BimN : ℝ) / BD) + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BreN : ℝ) / BD)) - ((x1.imR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BimN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BreN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P)) ≤ (riemannZeta (sOfG σ t)).im * 2 ^ P := by linarith [hbim.1]
    have hm := mul_le_mul_of_nonneg_left hlow hc3.le
    have : (imLo : ℝ) * (2 ^ P * BD * ED) ≤ (riemannZeta (sOfG σ t)).im * D * (2 ^ P * BD * ED) := by
      linarith [cast3, id_im_lo, hm]
    exact le_of_mul_le_mul_right this hk
  · rw [le_div_iff₀ hDR]
    have hup : (riemannZeta (sOfG σ t)).im * 2 ^ P ≤ (((x1.imP : ℝ) - x1.imN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BimN : ℝ) / BD) + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BreN : ℝ) / BD)) + ((x1.imR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BimN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BreN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P)) := by linarith [hbim.2]
    have hm := mul_le_mul_of_nonneg_left hup hc3.le
    have : (riemannZeta (sOfG σ t)).im * D * (2 ^ P * BD * ED) ≤ (imHi : ℝ) * (2 ^ P * BD * ED) := by
      linarith [cast4, id_im_hi, hm]
    exact le_of_mul_le_mul_right this hk

/-- **Soundness of the off-line kernel checker.**  If `checkG c o K N x1 x2 D … = true` and `x1`,
    `x2` are the `k = 0` accumulators of evaluator invariants after `N - 1` and `N` terms at
    `σ = (a - b)/q`, `t = tn / 2^tq`, then `reLo/D ≤ Re ζ(σ + i t) ≤ reHi/D` and likewise `Im`.  The
    remainder is `EMOff.em_zeta_orderK_enclosure_odd_ext` (general K, valid for `σ > -2K`). -/
theorem checkG_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N : ℕ) (x1 x2 : Acc)
    (h1 : AccOK c.P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK c.P (psumK σ t 0 N) x2) (D : ℕ)
    (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (hc : checkG c o K N x1 x2 D reLo reHi imLo imHi Qp Rn Rd = true) :
    ((reLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).re ∧ (riemannZeta (sOfG σ t)).re ≤ (reHi : ℝ) / D) ∧
    ((imLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).im ∧ (riemannZeta (sOfG σ t)).im ≤ (imHi : ℝ) / D) := by
  simp only [checkG, Bool.and_eq_true] at hc
  obtain ⟨hR, hcore⟩ := hc
  have hcore' := hcore
  simp only [checkCoreG, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hcore'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hN2⟩, _⟩, _⟩, hq1⟩, htn1⟩, _⟩, _⟩, _⟩, _⟩ := hcore'
  have hu : 0 < 2 ^ c.tq := Nat.two_pow_pos _
  have ht' : t = (c.tn : ℝ) / ((2 ^ c.tq : ℕ) : ℝ) := by rw [ht]; push_cast; ring
  have hE := remOddG_sound K N (by omega) o.a o.b o.q (2 ^ c.tq) c.tn (by omega) hu (by omega) σ t hσ
    ht' Qp Rn Rd hR
  exact checkCoreG_sound c.P c.tq c.tn K o.a o.b o.q N σ t hσ ht x1 x2 h1 h2 D reLo reHi imLo imHi
    _ _ hE hcore

/-- The `k = 0` accumulator of an invariant state. -/
theorem accOK_head (c : Cfg) (σ t : ℝ) (n : ℕ) (s : StO) (x : Acc) (xs : List Acc)
    (hI : InvO c σ t n s) (hs : s.acc = x :: xs) : AccOK c.P (psumK σ t 0 n) x := by
  obtain ⟨_, _, _, _, hA⟩ := hI
  rw [hs] at hA
  exact hA.1

end Off

end ArbEcon
