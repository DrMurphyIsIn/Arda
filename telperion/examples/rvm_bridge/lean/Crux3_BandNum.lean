/-
  Crux3_BandNum -- exact-rational ball arithmetic and the prime-side checker of the band certificate
  (rvm_bridge island, 2026-09-24, crux lane 3).

  conjecture1_proved = False.  Numerical analysis only.

  `InB x c r` means `|x - c| <= r` (`x` real, `c r` rational).  Sound ball operations (add, sub, mul,
  scalar, recentre, finite sums), and the enclosures the certificate needs, all proved here:
    * `le_log_of` / `log_le_of`: `log n` between two rationals from `exp(q) = exp(q/8)^8` and Mathlib's
      `Real.exp_bound` (Taylor with remainder), checked on rationals;
    * `inv_sqrt_between`: `1/sqrt n` from `q0^2 n <= 1 <= q1^2 n`;
    * `InB.cos_of` / `InB.sin_of`: `cos` / `sin` of an angle from a ball of the reduced angle
      `theta - 2 m pi`, `|cos a - cos b| <= |a - b|`, and KWin's Taylor remainders `KWin.cos_sub_tayl_le`.
  THE CHECKER.  A table entry `TEntry` (Lambda(n) = mu log n, log n in [lo, hi], 1/sqrt n in [q0, q1],
  reduction multiples) is validated by the Boolean `entryOK` (kernel-evaluated) and produces three
  output balls (`outB`); `entry_sound` proves the three real prime-side terms
  `2 Lambda(n)/sqrt n * gD(A, k_i, log n)` and `2 Lambda(n)/sqrt n * gX(log n)` lie in them, and that
  `log n < 2A` whenever `mu != 0`.
  No `sorry`.
-/
import Mathlib
import KWin_Taylor
import KWin_Data

open Finset

noncomputable section

namespace Crux3
/-! ## Rational balls: `InB x c r` means `|x - c| <= r` (x real, c r rational). -/

def InB (x : ℝ) (c r : ℚ) : Prop := |x - (c : ℝ)| ≤ (r : ℝ)

lemma InB.add {x y : ℝ} {c1 r1 c2 r2 : ℚ} (h1 : InB x c1 r1) (h2 : InB y c2 r2) :
    InB (x + y) (c1 + c2) (r1 + r2) := by
  unfold InB at *
  push_cast
  calc |x + y - (c1 + c2)| = |(x - c1) + (y - c2)| := by ring_nf
    _ ≤ |x - c1| + |y - c2| := abs_add_le _ _
    _ ≤ r1 + r2 := add_le_add h1 h2

lemma InB.sub {x y : ℝ} {c1 r1 c2 r2 : ℚ} (h1 : InB x c1 r1) (h2 : InB y c2 r2) :
    InB (x - y) (c1 - c2) (r1 + r2) := by
  unfold InB at *
  push_cast
  calc |x - y - (c1 - c2)| = |(x - c1) - (y - c2)| := by ring_nf
    _ ≤ |x - c1| + |y - c2| := abs_sub _ _
    _ ≤ r1 + r2 := add_le_add h1 h2

lemma InB.mul {x y : ℝ} {c1 r1 c2 r2 : ℚ} (h1 : InB x c1 r1) (h2 : InB y c2 r2) :
    InB (x * y) (c1 * c2) (|c1| * r2 + |c2| * r1 + r1 * r2) := by
  unfold InB at *
  push_cast
  have e : x * y - c1 * c2 = (c1 : ℝ) * (y - c2) + (c2 : ℝ) * (x - c1) + (x - c1) * (y - c2) := by ring
  rw [e]
  have hr1 : (0 : ℝ) ≤ r1 := le_trans (abs_nonneg _) h1
  calc |(c1 : ℝ) * (y - c2) + (c2 : ℝ) * (x - c1) + (x - c1) * (y - c2)|
      ≤ |(c1 : ℝ) * (y - c2)| + |(c2 : ℝ) * (x - c1)| + |(x - c1) * (y - c2)| := abs_add_three _ _ _
    _ = |(c1 : ℝ)| * |y - c2| + |(c2 : ℝ)| * |x - c1| + |x - c1| * |y - c2| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |(c1 : ℝ)| * r2 + |(c2 : ℝ)| * r1 + r1 * r2 := by
        gcongr

lemma InB.cmul {x : ℝ} {c r : ℚ} (q : ℚ) (h : InB x c r) : InB ((q : ℝ) * x) (q * c) (|q| * r) := by
  unfold InB at *
  push_cast
  rw [show (q : ℝ) * x - q * c = q * (x - c) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

lemma InB.recenter {x : ℝ} {c r : ℚ} (c' : ℚ) (h : InB x c r) : InB x c' (r + |c - c'|) := by
  unfold InB at *
  push_cast
  calc |x - c'| = |(x - c) + (c - c')| := by ring_nf
    _ ≤ |x - c| + |(c : ℝ) - c'| := abs_add_le _ _
    _ ≤ r + |(c : ℝ) - c'| := by linarith

lemma InB.mono {x : ℝ} {c r r' : ℚ} (h : InB x c r) (hr : r ≤ r') : InB x c r' := by
  unfold InB at *
  exact h.trans (by exact_mod_cast hr)

lemma InB.of_eq {x y : ℝ} {c r : ℚ} (h : InB x c r) (e : x = y) : InB y c r := e ▸ h

lemma InB.le {x : ℝ} {c r : ℚ} (h : InB x c r) : x ≤ ((c + r : ℚ) : ℝ) := by
  unfold InB at h
  push_cast
  linarith [le_abs_self (x - c)]

lemma InB.ge {x : ℝ} {c r : ℚ} (h : InB x c r) : ((c - r : ℚ) : ℝ) ≤ x := by
  unfold InB at h
  push_cast
  linarith [neg_abs_le (x - c)]

lemma InB.of_bounds {x : ℝ} {lo hi : ℚ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    InB x ((lo + hi) / 2) ((hi - lo) / 2) := by
  unfold InB
  push_cast
  rw [abs_le]
  constructor <;> linarith

lemma InB.zero : InB 0 0 0 := by unfold InB; simp

lemma InB.sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (c r : ι → ℚ) (h : ∀ i ∈ s, InB (x i) (c i) (r i)) :
    InB (∑ i ∈ s, x i) (∑ i ∈ s, c i) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [InB]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## exp and log enclosures from Mathlib's `Real.exp_bound`. -/

/-- `sum_{m < K} x^m/m!` over `ℚ`. -/
def expSQ (K : ℕ) (x : ℚ) : ℚ := ∑ m ∈ range K, x ^ m / (m.factorial : ℚ)
/-- The Taylor remainder bound `|x|^K (K+1)/(K! K)`. -/
def expRQ (K : ℕ) (x : ℚ) : ℚ := |x| ^ K * (((K + 1 : ℕ) : ℚ) / ((K.factorial : ℚ) * (K : ℚ)))

lemma exp_near (K : ℕ) (hK : 0 < K) {x : ℚ} (hx : |x| ≤ 1) :
    |Real.exp (x : ℝ) - (expSQ K x : ℝ)| ≤ (expRQ K x : ℝ) := by
  have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have h := Real.exp_bound hx' hK
  unfold expSQ expRQ
  push_cast
  simpa [Nat.succ_eq_add_one] using h

/-- `log n >= q` from `exp q <= n` with `exp(q/8)^8`. -/
lemma le_log_of (K : ℕ) (hK : 0 < K) {q : ℚ} (n : ℕ) (hn : 0 < n) (hq : |q / 8| ≤ 1)
    (hc : (expSQ K (q / 8) + expRQ K (q / 8)) ^ 8 ≤ (n : ℚ)) : (q : ℝ) ≤ Real.log n := by
  have h := exp_near K hK hq
  have hup : Real.exp ((q / 8 : ℚ) : ℝ) ≤ ((expSQ K (q / 8) + expRQ K (q / 8) : ℚ) : ℝ) := by
    have := le_abs_self (Real.exp ((q / 8 : ℚ) : ℝ) - (expSQ K (q / 8) : ℝ))
    rw [Rat.cast_add]
    linarith
  have h8 : Real.exp (q : ℝ) = Real.exp ((q / 8 : ℚ) : ℝ) ^ 8 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hpow : Real.exp ((q / 8 : ℚ) : ℝ) ^ 8 ≤ ((expSQ K (q / 8) + expRQ K (q / 8) : ℚ) : ℝ) ^ 8 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hup 8
  have hcR : ((expSQ K (q / 8) + expRQ K (q / 8) : ℚ) : ℝ) ^ 8 ≤ (n : ℝ) := by exact_mod_cast hc
  rw [Real.le_log_iff_exp_le (by exact_mod_cast hn), h8]
  linarith

/-- `log n <= q` from `n <= exp q`. -/
lemma log_le_of (K : ℕ) (hK : 0 < K) {q : ℚ} (n : ℕ) (hn : 0 < n) (hq : |q / 8| ≤ 1)
    (hpos : 0 ≤ expSQ K (q / 8) - expRQ K (q / 8))
    (hc : (n : ℚ) ≤ (expSQ K (q / 8) - expRQ K (q / 8)) ^ 8) : Real.log n ≤ (q : ℝ) := by
  have h := exp_near K hK hq
  have hlo : ((expSQ K (q / 8) - expRQ K (q / 8) : ℚ) : ℝ) ≤ Real.exp ((q / 8 : ℚ) : ℝ) := by
    have := neg_abs_le (Real.exp ((q / 8 : ℚ) : ℝ) - (expSQ K (q / 8) : ℝ))
    rw [Rat.cast_sub]
    linarith
  have h8 : Real.exp (q : ℝ) = Real.exp ((q / 8 : ℚ) : ℝ) ^ 8 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hposR : (0 : ℝ) ≤ ((expSQ K (q / 8) - expRQ K (q / 8) : ℚ) : ℝ) := by exact_mod_cast hpos
  have hpow : ((expSQ K (q / 8) - expRQ K (q / 8) : ℚ) : ℝ) ^ 8 ≤ Real.exp ((q / 8 : ℚ) : ℝ) ^ 8 :=
    pow_le_pow_left₀ hposR hlo 8
  have hcR : (n : ℝ) ≤ ((expSQ K (q / 8) - expRQ K (q / 8) : ℚ) : ℝ) ^ 8 := by exact_mod_cast hc
  rw [Real.log_le_iff_le_exp (by exact_mod_cast hn), h8]
  linarith

/-- `1/sqrt n` between two rationals. -/
lemma inv_sqrt_between {n : ℕ} (hn : 0 < n) {q0 q1 : ℚ} (h0 : 0 ≤ q0) (h1 : q0 ^ 2 * n ≤ 1)
    (h2 : 1 ≤ q1 ^ 2 * n) (h3 : 0 ≤ q1) :
    (q0 : ℝ) ≤ 1 / Real.sqrt n ∧ 1 / Real.sqrt n ≤ (q1 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hnR.le
  have h1R : (q0 : ℝ) ^ 2 * n ≤ 1 := by exact_mod_cast h1
  have h2R : 1 ≤ (q1 : ℝ) ^ 2 * n := by exact_mod_cast h2
  have h0R : (0 : ℝ) ≤ q0 := by exact_mod_cast h0
  have h3R : (0 : ℝ) ≤ q1 := by exact_mod_cast h3
  have hx0 : 0 ≤ (q0 : ℝ) * Real.sqrt n := mul_nonneg h0R hs.le
  have hx1 : 0 ≤ (q1 : ℝ) * Real.sqrt n := mul_nonneg h3R hs.le
  have e0 : ((q0 : ℝ) * Real.sqrt n) ^ 2 = (q0 : ℝ) ^ 2 * n := by rw [mul_pow, hsq]
  have e1 : ((q1 : ℝ) * Real.sqrt n) ^ 2 = (q1 : ℝ) ^ 2 * n := by rw [mul_pow, hsq]
  constructor
  · rw [le_div_iff₀ hs]
    have : ((q0 : ℝ) * Real.sqrt n) ^ 2 ≤ 1 := by rw [e0]; exact h1R
    exact (pow_le_one_iff_of_nonneg hx0 (by norm_num)).mp this
  · rw [div_le_iff₀ hs]
    have : 1 ≤ ((q1 : ℝ) * Real.sqrt n) ^ 2 := by rw [e1]; exact h2R
    exact (one_le_pow_iff_of_nonneg hx1 (by norm_num)).mp this

/-! ## cos / sin enclosures: periodicity, recentring, and KWin's Taylor remainders. -/

/-- `KWin.tayl` over `ℚ`. -/
def taylQ (par M : ℕ) (y : ℚ) : ℚ := ∑ m ∈ range M, (-1) ^ m * y ^ (2 * m + par) / ((2 * m + par).factorial : ℚ)

lemma taylQ_cast (par M : ℕ) (y : ℚ) : ((taylQ par M y : ℚ) : ℝ) = KWin.tayl par M (y : ℝ) := by
  unfold taylQ KWin.tayl
  push_cast
  rfl

/-- `cos θ` from a ball of `θ - 2 m π`. -/
lemma InB.cos_of {θ : ℝ} {c r : ℚ} (M : ℕ) (m : ℤ) (h : InB (θ - m * (2 * Real.pi)) c r)
    (hM : |c| ≤ ((2 * M + 1 : ℕ) : ℚ) / 2) :
    InB (Real.cos θ) (taylQ 0 M c) (2 * |c| ^ (2 * M) / ((2 * M).factorial : ℚ) + r) := by
  unfold InB at *
  have e : Real.cos θ = Real.cos (θ - m * (2 * Real.pi)) := (Real.cos_sub_int_mul_two_pi θ m).symm
  rw [e, taylQ_cast]
  have hM' : |(c : ℝ)| ≤ (2 * M + 1) / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hM
    push_cast at this
    simpa using this
  have t := KWin.cos_sub_tayl_le hM'
  have l := Real.abs_cos_sub_cos_le (θ - m * (2 * Real.pi)) c
  push_cast
  calc |Real.cos (θ - m * (2 * Real.pi)) - KWin.tayl 0 M c|
      ≤ |Real.cos (θ - m * (2 * Real.pi)) - Real.cos c| + |Real.cos c - KWin.tayl 0 M c| := abs_sub_le _ _ _
    _ ≤ r + 2 * |(c : ℝ)| ^ (2 * M) / ((2 * M).factorial : ℝ) := add_le_add (l.trans h) t
    _ = _ := by ring

/-- `sin θ` from a ball of `θ - 2 m π`. -/
lemma InB.sin_of {θ : ℝ} {c r : ℚ} (M : ℕ) (m : ℤ) (h : InB (θ - m * (2 * Real.pi)) c r)
    (hM : |c| ≤ ((2 * M + 1 + 1 : ℕ) : ℚ) / 2) :
    InB (Real.sin θ) (taylQ 1 M c) (2 * |c| ^ (2 * M + 1) / ((2 * M + 1).factorial : ℚ) + r) := by
  unfold InB at *
  have e : Real.sin θ = Real.sin (θ - m * (2 * Real.pi)) := (Real.sin_sub_int_mul_two_pi θ m).symm
  rw [e, taylQ_cast]
  have hM' : |(c : ℝ)| ≤ (2 * M + 1 + 1) / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hM
    push_cast at this
    simpa using this
  have t := KWin.sin_sub_tayl_le hM'
  have l := Real.abs_sin_sub_sin_le (θ - m * (2 * Real.pi)) c
  push_cast
  calc |Real.sin (θ - m * (2 * Real.pi)) - KWin.tayl 1 M c|
      ≤ |Real.sin (θ - m * (2 * Real.pi)) - Real.sin c| + |Real.sin c - KWin.tayl 1 M c| := abs_sub_le _ _ _
    _ ≤ r + 2 * |(c : ℝ)| ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) := add_le_add (l.trans h) t
    _ = _ := by ring


/-! ## The prime-side checker: one table entry per `n`. -/

/-- One table entry: `Λ(n) = mu log n`, `log n ∈ [lo, hi]`, `1/sqrt n ∈ [q0, q1]`, and the
reduction multiples `m1, m2` for the angles `k_i log n`. -/
structure TEntry where
  mu : ℚ
  lo : ℚ
  hi : ℚ
  q0 : ℚ
  q1 : ℚ
  m1 : ℤ
  m2 : ℤ

/-- The band parameters: `A = Q π`, frequencies `k1, k2`, sign product `s12 = s1 s2`. -/
structure BandP where
  Q : ℚ
  k1 : ℚ
  k2 : ℚ
  s12 : ℚ

/-- `Real.pi_gt_d20` / `Real.pi_lt_d20`. -/
def PLOq : ℚ := 314159265358979323846 / 10 ^ 20
def PHIq : ℚ := 314159265358979323847 / 10 ^ 20
def KX : ℕ := 22
def MT : ℕ := 15
def RD : ℕ := 18
def RT : ℕ := 24

lemma pi_InB : InB Real.pi ((PLOq + PHIq) / 2) ((PHIq - PLOq) / 2) := by
  apply InB.of_bounds
  · have := Real.pi_gt_d20; unfold PLOq; push_cast; linarith
  · have := Real.pi_lt_d20; unfold PHIq; push_cast; linarith

def bAdd (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 + b.1, a.2 + b.2)
def bSub (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 - b.1, a.2 + b.2)
def bMul (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 * b.1, |a.1| * b.2 + |b.1| * a.2 + a.2 * b.2)
def bC (q : ℚ) (a : ℚ × ℚ) : ℚ × ℚ := (q * a.1, |q| * a.2)
def bRound (a : ℚ × ℚ) (R : ℕ) : ℚ × ℚ := (KWin.floorR a.1 R, a.2 + |a.1 - KWin.floorR a.1 R|)
def piB : ℚ × ℚ := ((PLOq + PHIq) / 2, (PHIq - PLOq) / 2)
def cosB (a : ℚ × ℚ) : ℚ × ℚ := (taylQ 0 MT a.1, 2 * |a.1| ^ (2 * MT) / ((2 * MT).factorial : ℚ) + a.2)
def sinB (a : ℚ × ℚ) : ℚ × ℚ := (taylQ 1 MT a.1, 2 * |a.1| ^ (2 * MT + 1) / ((2 * MT + 1).factorial : ℚ) + a.2)

def yB (E : TEntry) : ℚ × ℚ := ((E.lo + E.hi) / 2, (E.hi - E.lo) / 2)
def sB (E : TEntry) : ℚ × ℚ := ((E.q0 + E.q1) / 2, (E.q1 - E.q0) / 2)
def phiB (k : ℚ) (E : TEntry) (m : ℤ) : ℚ × ℚ := bRound (bSub (bC k (yB E)) (bC (2 * m) piB)) RD
def wB (E : TEntry) : ℚ × ℚ := bMul (bC (2 * E.mu) (yB E)) (sB E)
def tAyB (P : BandP) (E : TEntry) : ℚ × ℚ := bSub (bC 2 (bC P.Q piB)) (yB E)
def gD1B (P : BandP) (E : TEntry) : ℚ × ℚ :=
  bAdd (bC (1 / 2) (bMul (tAyB P E) (cosB (phiB P.k1 E E.m1)))) (bC (1 / (2 * P.k1)) (sinB (phiB P.k1 E E.m1)))
def gD2B (P : BandP) (E : TEntry) : ℚ × ℚ :=
  bAdd (bC (1 / 2) (bMul (tAyB P E) (cosB (phiB P.k2 E E.m2)))) (bC (1 / (2 * P.k2)) (sinB (phiB P.k2 E E.m2)))
def gXB (P : BandP) (E : TEntry) : ℚ × ℚ :=
  bC (P.s12 / (P.k1 ^ 2 - P.k2 ^ 2))
    (bSub (bC P.k1 (sinB (phiB P.k2 E E.m2))) (bC P.k2 (sinB (phiB P.k1 E E.m1))))

/-- The three output balls of an entry (zero when `mu = 0`). -/
def outB (P : BandP) (E : TEntry) : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) :=
  if E.mu = 0 then ((0, 0), (0, 0), (0, 0))
  else (bRound (bMul (wB E) (gD1B P E)) RT, bRound (bMul (wB E) (gD2B P E)) RT,
    bRound (bMul (wB E) (gXB P E)) RT)

/-- The Boolean check of an entry. -/
def entryOK (P : BandP) (n : ℕ) (E : TEntry) : Bool :=
  decide (E.mu = 0) ||
  (decide (0 < n) && decide (|E.lo / 8| ≤ 1) && decide (|E.hi / 8| ≤ 1) &&
   decide ((expSQ KX (E.lo / 8) + expRQ KX (E.lo / 8)) ^ 8 ≤ (n : ℚ)) &&
   decide (0 ≤ expSQ KX (E.hi / 8) - expRQ KX (E.hi / 8)) &&
   decide ((n : ℚ) ≤ (expSQ KX (E.hi / 8) - expRQ KX (E.hi / 8)) ^ 8) &&
   decide (0 ≤ E.q0) && decide (E.q0 ^ 2 * n ≤ 1) && decide (1 ≤ E.q1 ^ 2 * n) && decide (0 ≤ E.q1) &&
   decide (|(phiB P.k1 E E.m1).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2) &&
   decide (|(phiB P.k2 E E.m2).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2) &&
   decide (E.hi < 2 * P.Q * PLOq))

lemma InB.bAdd {x y : ℝ} {a b : ℚ × ℚ} (h1 : InB x a.1 a.2) (h2 : InB y b.1 b.2) :
    InB (x + y) (bAdd a b).1 (bAdd a b).2 := h1.add h2
lemma InB.bSub {x y : ℝ} {a b : ℚ × ℚ} (h1 : InB x a.1 a.2) (h2 : InB y b.1 b.2) :
    InB (x - y) (bSub a b).1 (bSub a b).2 := h1.sub h2
lemma InB.bMul {x y : ℝ} {a b : ℚ × ℚ} (h1 : InB x a.1 a.2) (h2 : InB y b.1 b.2) :
    InB (x * y) (bMul a b).1 (bMul a b).2 := h1.mul h2
lemma InB.bC {x : ℝ} {a : ℚ × ℚ} (q : ℚ) (h : InB x a.1 a.2) :
    InB ((q : ℝ) * x) (bC q a).1 (bC q a).2 := h.cmul q
lemma InB.bRound {x : ℝ} {a : ℚ × ℚ} (R : ℕ) (h : InB x a.1 a.2) :
    InB x (bRound a R).1 (bRound a R).2 := h.recenter _

/-- The prime-side term shapes. -/
def gDr (A k y : ℝ) : ℝ := (2 * A - y) * Real.cos (k * y) / 2 + Real.sin (k * y) / (2 * k)
def gXr (k1 k2 s12 y : ℝ) : ℝ := s12 * (k1 * Real.sin (k2 * y) - k2 * Real.sin (k1 * y)) / (k1 ^ 2 - k2 ^ 2)

/-- **Soundness of one entry.** -/
theorem entry_sound (P : BandP) (hQ : 0 ≤ P.Q) (n : ℕ) (E : TEntry) (hok : entryOK P n E = true)
    (hlam : ArithmeticFunction.vonMangoldt n = (E.mu : ℝ) * Real.log n) :
    InB (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gDr ((P.Q : ℝ) * Real.pi) P.k1 (Real.log n))
        (outB P E).1.1 (outB P E).1.2
      ∧ InB (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gDr ((P.Q : ℝ) * Real.pi) P.k2 (Real.log n))
        (outB P E).2.1.1 (outB P E).2.1.2
      ∧ InB (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gXr P.k1 P.k2 P.s12 (Real.log n))
        (outB P E).2.2.1 (outB P E).2.2.2
      ∧ (E.mu ≠ 0 → Real.log n < 2 * ((P.Q : ℝ) * Real.pi)) := by
  by_cases hmu : E.mu = 0
  · have hl : ArithmeticFunction.vonMangoldt n = 0 := by rw [hlam, hmu]; simp
    simp only [outB, hmu, if_true, hl]
    refine ⟨?_, ?_, ?_, fun h => absurd rfl h⟩ <;> simp [InB]
  · have hok' := hok
    unfold entryOK at hok'
    simp only [hmu, decide_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hlo8⟩, hhi8⟩, hexp1⟩, hexp2⟩, hexp3⟩, hq0⟩, hq01⟩, hq11⟩, hq1⟩, hph1⟩, hph2⟩, hA⟩ := hok'
    simp only [outB, hmu, if_false]
    -- the real inputs
    have hy : InB (Real.log n) (yB E).1 (yB E).2 := by
      apply InB.of_bounds
      · exact le_log_of KX (by unfold KX; norm_num) n hn hlo8 hexp1
      · exact log_le_of KX (by unfold KX; norm_num) n hn hhi8 hexp2 hexp3
    have hs : InB (1 / Real.sqrt n) (sB E).1 (sB E).2 := by
      obtain ⟨a, b⟩ := inv_sqrt_between hn hq0 hq01 hq11 hq1
      exact InB.of_bounds a b
    have hpi : InB Real.pi piB.1 piB.2 := pi_InB
    have hw : InB (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n) (wB E).1 (wB E).2 := by
      have := (hy.bC (2 * E.mu)).bMul hs
      refine this.of_eq ?_
      rw [hlam]; push_cast; ring
    have hphi : ∀ (k : ℚ) (m : ℤ), InB ((k : ℝ) * Real.log n - m * (2 * Real.pi)) (phiB k E m).1 (phiB k E m).2 := by
      intro k m
      have := ((hy.bC k).bSub (hpi.bC (2 * m))).bRound RD
      refine this.of_eq ?_
      push_cast; ring
    have hc : ∀ (k : ℚ) (m : ℤ), |(phiB k E m).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2 →
        InB (Real.cos ((k : ℝ) * Real.log n)) (cosB (phiB k E m)).1 (cosB (phiB k E m)).2 := by
      intro k m hm
      have := InB.cos_of MT m (hphi k m) hm
      unfold cosB
      refine this.mono (le_of_eq ?_)
      ring
    have hsn : ∀ (k : ℚ) (m : ℤ), |(phiB k E m).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2 →
        InB (Real.sin ((k : ℝ) * Real.log n)) (sinB (phiB k E m)).1 (sinB (phiB k E m)).2 := by
      intro k m hm
      have hm' : |(phiB k E m).1| ≤ ((2 * MT + 1 + 1 : ℕ) : ℚ) / 2 := by
        refine hm.trans ?_
        push_cast
        linarith
      have := InB.sin_of MT m (hphi k m) hm'
      unfold sinB
      refine this.mono (le_of_eq ?_)
      ring
    have htA : InB (2 * ((P.Q : ℝ) * Real.pi) - Real.log n) (tAyB P E).1 (tAyB P E).2 := by
      have := ((hpi.bC P.Q).bC 2).bSub hy
      refine this.of_eq ?_
      push_cast; ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hg : InB (gDr ((P.Q : ℝ) * Real.pi) P.k1 (Real.log n)) (gD1B P E).1 (gD1B P E).2 := by
        have := ((htA.bMul (hc P.k1 E.m1 hph1)).bC (1 / 2)).bAdd ((hsn P.k1 E.m1 hph1).bC (1 / (2 * P.k1)))
        refine this.of_eq ?_
        unfold gDr; push_cast; ring
      exact (hw.bMul hg).bRound RT
    · have hg : InB (gDr ((P.Q : ℝ) * Real.pi) P.k2 (Real.log n)) (gD2B P E).1 (gD2B P E).2 := by
        have := ((htA.bMul (hc P.k2 E.m2 hph2)).bC (1 / 2)).bAdd ((hsn P.k2 E.m2 hph2).bC (1 / (2 * P.k2)))
        refine this.of_eq ?_
        unfold gDr; push_cast; ring
      exact (hw.bMul hg).bRound RT
    · have hg : InB (gXr P.k1 P.k2 P.s12 (Real.log n)) (gXB P E).1 (gXB P E).2 := by
        have := (((hsn P.k2 E.m2 hph2).bC P.k1).bSub ((hsn P.k1 E.m1 hph1).bC P.k2)).bC
          (P.s12 / (P.k1 ^ 2 - P.k2 ^ 2))
        refine this.of_eq ?_
        unfold gXr; push_cast; ring
      exact (hw.bMul hg).bRound RT
    · intro _
      have h1 := hy.le
      have h2 : ((E.lo + E.hi) / 2 + (E.hi - E.lo) / 2 : ℚ) = E.hi := by ring
      unfold yB at h1
      simp only at h1
      rw [h2] at h1
      have h3 : ((E.hi : ℚ) : ℝ) < ((2 * P.Q * PLOq : ℚ) : ℝ) := by exact_mod_cast hA
      have h4 := Real.pi_gt_d20
      push_cast at h3
      have hPL : (PLOq : ℝ) ≤ Real.pi := by unfold PLOq; push_cast; linarith
      have hQR : (0 : ℝ) ≤ P.Q := by exact_mod_cast hQ
      have h5 : 2 * (P.Q : ℝ) * PLOq ≤ 2 * ((P.Q : ℝ) * Real.pi) := by nlinarith
      linarith

end Crux3
