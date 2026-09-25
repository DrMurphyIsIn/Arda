/-  Arb4_Gamma.lean -- lane Arb4 (h1000 compaction): the Γℝ argument-change side conditions of a
    Turing band (brick K6b, `ArgGammaR`) as ONE Boolean kernel check.

    `ArgChangeGlue.K6Side` compares the band's enclosures `[L4, H4]`, `[L5, H5]` with the closed-form
    brackets `Sm1`, `S2` of `ArgGammaR` at the two edge heights.  The generated module
    `ArgChangeH1000` proves one `log` box, one `arctan` box and one `S2`/`Sm1` box per height by
    `norm_num` over truncated series (about 1 MB of olean per height).  Here:

      * `logOK logLo logHi`, `log_mem`  -- `log v = k log 2 + log (1 - x)`, `v = 2^k (1 - x)`,
                             `0 ≤ x < 1`, with `RSDesignTheta.log2_box` and the Taylor bracket
                             `ArgGammaR.log_one_sub_mem` (n terms);
      * `atanOK arctanLo arctanHi`, `arctan_mem` -- `arctan y` by the Taylor bracket
                             `ArctanTaylor.arctan_bracket` (mode 0, `0 ≤ y ≤ 1`), by
                             `arctan y = π/2 - arctan (1/y)` (mode 1, `y > 0`), or `π/4` (`y = 1`);
      * `GamD`, `gamOK`, `S2_mem`, `Sm1_mem` -- the brackets at one height (`ArgGammaR.S2_mem_of`,
                             `Sm1_mem_of`, `RSDesignTheta.logpi_box`, `π` to 20 digits);
      * `k6B`, `k6B_sound` -- the four K6b comparisons of a band from two heights.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/
import Arb4_Edge
import ArgGammaR

open scoped Real

namespace Arb4

open Q

/-! ## A. Constants -/

/-- `log 2` bracket (`RSDesignTheta.log2_box`). -/
def l2lo : Q := frac 3465735902799708427977 5000000000000000000000
def l2hi : Q := frac 6931471805599487910229 10000000000000000000000

/-- `log π` bracket (`RSDesignTheta.logpi_box`). -/
def lplo : Q := frac 11447298858493313056567 10000000000000000000000
def lphi : Q := frac 5723649429247365361409 5000000000000000000000

/-- `π` bracket (`Real.pi_gt_d20`, `Real.pi_lt_d20`). -/
def pilo : Q := frac 314159265358979323846 100000000000000000000
def pihi : Q := frac 314159265358979323847 100000000000000000000

theorem log2_mem : l2lo.val ≤ Real.log 2 ∧ Real.log 2 ≤ l2hi.val := by
  obtain ⟨h1, h2⟩ := RSDesignTheta.log2_box
  rw [l2lo, l2hi, val_frac _ (by norm_num), val_frac _ (by norm_num)]
  push_cast
  exact ⟨h1, h2⟩

theorem logpi_mem : lplo.val ≤ Real.log π ∧ Real.log π ≤ lphi.val := by
  obtain ⟨h1, h2⟩ := RSDesignTheta.logpi_box
  rw [lplo, lphi, val_frac _ (by norm_num), val_frac _ (by norm_num)]
  push_cast
  exact ⟨h1, h2⟩

theorem pi_mem : pilo.val ≤ π ∧ π ≤ pihi.val := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [pilo, pihi, val_frac _ (by norm_num), val_frac _ (by norm_num)]
  push_cast
  norm_num at h1 h2 ⊢
  exact ⟨h1.le, h2.le⟩

/-! ## B. Logarithms -/

/-- `2^k` for an integer `k`. -/
def pow2Q (k : ℤ) : Q := if 0 ≤ k then ofNat (2 ^ k.toNat) else frac 1 (2 ^ (-k).toNat)

theorem val_pow2Q (k : ℤ) : (pow2Q k).val = (2 : ℝ) ^ k := by
  unfold pow2Q
  by_cases h : 0 ≤ k
  · rw [if_pos h, val_ofNat]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    push_cast
    simp
  · rw [if_neg h, val_frac _ Nat.one_le_two_pow]
    push Not at h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -k = m := ⟨(-k).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hk : k = -(m : ℤ) := by omega
    rw [hk, zpow_neg, zpow_natCast]
    simp

theorem pow2Q_n_pos (k : ℤ) : 0 < (pow2Q k).n := by
  unfold pow2Q
  by_cases h : 0 ≤ k
  · rw [if_pos h]; show (0 : ℤ) < ((2 ^ k.toNat : ℕ) : ℤ); exact_mod_cast Nat.two_pow_pos _
  · rw [if_neg h]; show (0 : ℤ) < 1; norm_num

/-- `Σ_{i<n} x^(i+1)/(i+1)`. -/
def lserQ (x : Q) (n : ℕ) : Q := sumQ (fun i => div (npow x (i + 1)) (ofNat (i + 1))) n

theorem val_lserQ (x : Q) (n : ℕ) :
    (lserQ x n).val = ∑ i ∈ Finset.range n, x.val ^ (i + 1) / (i + 1) := by
  rw [lserQ, val_sumQ]
  apply Finset.sum_congr rfl
  intro i _
  rw [val_div _ (by show (0 : ℤ) < ((i + 1 : ℕ) : ℤ); exact_mod_cast Nat.succ_pos i), val_npow,
    val_ofNat]
  push_cast; ring

/-- `x = 1 - v / 2^k`. -/
def lx (v : Q) (k : ℤ) : Q := sub (ofNat 1) (div v (pow2Q k))

/-- The certificate `(k, n)` of `log v` is admissible: `v > 0`, `0 ≤ x < 1`. -/
def logOK (v : Q) (k : ℤ) : Bool := lt (ofNat 0) v && decide (0 ≤ (lx v k).n) && lt (lx v k) (ofNat 1)

/-- `k log 2`, bracketed. -/
def kl2lo (k : ℤ) : Q := if 0 ≤ k then mul (ofInt k) l2lo else mul (ofInt k) l2hi
def kl2hi (k : ℤ) : Q := if 0 ≤ k then mul (ofInt k) l2hi else mul (ofInt k) l2lo

theorem kl2_mem (k : ℤ) : (kl2lo k).val ≤ k * Real.log 2 ∧ k * Real.log 2 ≤ (kl2hi k).val := by
  obtain ⟨h1, h2⟩ := log2_mem
  unfold kl2lo kl2hi
  by_cases h : 0 ≤ k
  · rw [if_pos h, if_pos h, val_mul, val_mul, val_ofInt]
    have hk : (0 : ℝ) ≤ k := by exact_mod_cast h
    exact ⟨mul_le_mul_of_nonneg_left h1 hk, mul_le_mul_of_nonneg_left h2 hk⟩
  · rw [if_neg h, if_neg h, val_mul, val_mul, val_ofInt]
    have hk : (k : ℝ) ≤ 0 := by push Not at h; exact_mod_cast h.le
    exact ⟨mul_le_mul_of_nonpos_left h2 hk, mul_le_mul_of_nonpos_left h1 hk⟩

/-- `1 - x` (the divisor of the Taylor remainder). -/
def omx (x : Q) : Q := sub (ofNat 1) x

theorem omx_n_pos {x : Q} (h : lt x (ofNat 1) = true) : 0 < (omx x).n := by
  have h' : x.n * ((0 : ℕ) + 1 : ℤ) < ((1 : ℕ) : ℤ) * ((x.dm : ℤ) + 1) := of_decide_eq_true h
  show 0 < ((1 : ℕ) : ℤ) * ((x.dm : ℤ) + 1) - x.n * ((0 : ℕ) + 1 : ℤ)
  linarith

/-- Lower and upper bounds of `log v` from the certificate `(k, n)`. -/
def logLo (v : Q) (k : ℤ) (n : ℕ) : Q :=
  sub (sub (kl2lo k) (lserQ (lx v k) n)) (div (npow (lx v k) (n + 1)) (omx (lx v k)))

def logHi (v : Q) (k : ℤ) (n : ℕ) : Q :=
  add (sub (kl2hi k) (lserQ (lx v k) n)) (div (npow (lx v k) (n + 1)) (omx (lx v k)))

theorem log_mem (v : Q) (k : ℤ) (n : ℕ) (h : logOK v k = true) :
    (logLo v k n).val ≤ Real.log v.val ∧ Real.log v.val ≤ (logHi v k n).val := by
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hx0⟩, hx1⟩ := h
  set x := lx v k with hx
  have hv' := lt_sound hv
  rw [val_ofNat, Nat.cast_zero] at hv'
  have hx0' : 0 ≤ x.val := val_nonneg hx0
  have hx1' := lt_sound hx1
  rw [val_ofNat, Nat.cast_one] at hx1'
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hxv : x.val = 1 - v.val / (2 : ℝ) ^ k := by
    rw [hx, lx, val_sub, val_ofNat, val_div _ (pow2Q_n_pos k), val_pow2Q, Nat.cast_one]
  have hveq : v.val = (2 : ℝ) ^ k * (1 - x.val) := by
    rw [hxv]; field_simp; ring
  have hpos1 : (0 : ℝ) < 1 - x.val := by linarith
  have hlog : Real.log v.val = k * Real.log 2 + Real.log (1 - x.val) := by
    rw [hveq, Real.log_mul (ne_of_gt h2k) (ne_of_gt hpos1), Real.log_zpow]
  have hser := ArgGammaR.log_one_sub_mem hx0' hx1' n
  have hk := kl2_mem k
  have homx : (omx x).val = 1 - x.val := by rw [omx, val_sub, val_ofNat, Nat.cast_one]
  have hdiv : (div (npow x (n + 1)) (omx x)).val = x.val ^ (n + 1) / (1 - x.val) := by
    rw [val_div _ (omx_n_pos hx1), val_npow, homx]
  unfold logLo logHi
  rw [← hx, val_sub, val_sub, val_add, val_sub, val_lserQ, hdiv, hlog]
  constructor <;> linarith [hser.1, hser.2, hk.1, hk.2]

/-! ## C. Arctangents -/

/-- `atanPS u N = Σ_{j<N} (-1)^j u^(2j+1)/(2j+1)`. -/
def atanPSQ (u : Q) (N : ℕ) : Q :=
  sumQ (fun j => mul (ofInt ((-1) ^ j)) (div (npow u (2 * j + 1)) (ofNat (2 * j + 1)))) N

/-- The Taylor remainder `u^(2N+1)/(2N+1)`. -/
def atanErrQ (u : Q) (N : ℕ) : Q := div (npow u (2 * N + 1)) (ofNat (2 * N + 1))

theorem odd_n_pos (j : ℕ) : 0 < (ofNat (2 * j + 1)).n := by
  show (0 : ℤ) < ((2 * j + 1 : ℕ) : ℤ); exact_mod_cast Nat.succ_pos _

theorem val_atanPSQ (u : Q) (N : ℕ) : (atanPSQ u N).val = ArctanTaylor.atanPS u.val N := by
  rw [atanPSQ, val_sumQ, ArctanTaylor.atanPS]
  apply Finset.sum_congr rfl
  intro j _
  rw [val_mul, val_ofInt, val_div _ (odd_n_pos j), val_npow, val_ofNat]
  push_cast; ring

theorem val_atanErrQ (u : Q) (N : ℕ) : (atanErrQ u N).val = u.val ^ (2 * N + 1) / (2 * N + 1) := by
  rw [atanErrQ, val_div _ (odd_n_pos N), val_npow, val_ofNat]
  push_cast; ring

/-- The reciprocal `1 / y`. -/
def inv (y : Q) : Q := div (ofNat 1) y

/-- Admissibility of an arctangent certificate: mode 0 needs `0 ≤ y ≤ 1`, mode 1 `y > 0`, mode 2
    `y = 1`. -/
def atanOK (y : Q) : ℕ → Bool
  | 0 => le (ofNat 0) y && le y (ofNat 1)
  | 1 => lt (ofNat 0) y
  | _ => eqB y (ofNat 1)

/-- Lower bound of `arctan y`. -/
def arctanLo (y : Q) (N : ℕ) : ℕ → Q
  | 0 => sub (atanPSQ y N) (atanErrQ y N)
  | 1 => sub (div pilo (ofNat 2)) (add (atanPSQ (inv y) N) (atanErrQ (inv y) N))
  | _ => div pilo (ofNat 4)

/-- Upper bound of `arctan y`. -/
def arctanHi (y : Q) (N : ℕ) : ℕ → Q
  | 0 => add (atanPSQ y N) (atanErrQ y N)
  | 1 => sub (div pihi (ofNat 2)) (sub (atanPSQ (inv y) N) (atanErrQ (inv y) N))
  | _ => div pihi (ofNat 4)

theorem two_n_pos : 0 < (ofNat 2).n := by show (0 : ℤ) < ((2 : ℕ) : ℤ); norm_num
theorem four_n_pos : 0 < (ofNat 4).n := by show (0 : ℤ) < ((4 : ℕ) : ℤ); norm_num

theorem arctan_mem (y : Q) (N mode : ℕ) (h : atanOK y mode = true) :
    (arctanLo y N mode).val ≤ Real.arctan y.val ∧ Real.arctan y.val ≤ (arctanHi y N mode).val := by
  obtain ⟨hpl, hph⟩ := pi_mem
  match mode, h with
  | 0, h =>
    simp only [atanOK, Bool.and_eq_true] at h
    have h0 := le_sound h.1
    rw [val_ofNat, Nat.cast_zero] at h0
    have hb := ArctanTaylor.arctan_bracket y.val h0 N
    rw [abs_le] at hb
    simp only [arctanLo, arctanHi]
    rw [val_sub, val_add, val_atanPSQ, val_atanErrQ]
    constructor <;> linarith [hb.1, hb.2]
  | 1, h =>
    simp only [atanOK] at h
    have hy := lt_sound h
    rw [val_ofNat, Nat.cast_zero] at hy
    have hyn : 0 < y.n := by
      by_contra hn
      push Not at hn
      have : y.val ≤ 0 := by
        have : (y.n : ℝ) ≤ 0 := by exact_mod_cast hn
        exact div_nonpos_of_nonpos_of_nonneg this (den_pos y).le
      linarith
    have hinv : (inv y).val = y.val⁻¹ := by
      rw [inv, val_div _ hyn, val_ofNat, Nat.cast_one, one_div]
    have hu : 0 ≤ (inv y).val := by rw [hinv]; exact inv_nonneg.mpr hy.le
    have hb := ArctanTaylor.arctan_bracket (inv y).val hu N
    rw [abs_le] at hb
    have hr := Real.arctan_inv_of_pos hy
    rw [← hinv] at hr
    simp only [arctanLo, arctanHi]
    rw [val_sub, val_div _ two_n_pos, val_add, val_atanPSQ, val_atanErrQ, val_sub,
      val_div _ two_n_pos, val_sub, val_atanPSQ, val_atanErrQ, val_ofNat]
    push_cast
    constructor <;> linarith [hb.1, hb.2]
  | m + 2, h =>
    simp only [atanOK] at h
    have hy := eqB_sound h
    rw [val_ofNat, Nat.cast_one] at hy
    simp only [arctanLo, arctanHi]
    rw [val_div _ four_n_pos, val_div _ four_n_pos, val_ofNat, hy, Real.arctan_one]
    push_cast
    constructor <;> linarith

/-! ## D. The closed-form Γℝ brackets at one height -/

/-- The certificate of the brackets at one height `T`: `log (1 + T²/4)` (`k2`, `n2`),
    `log (1/4 + T²/4)` (`km`, `nm`), `arctan (T/2)` (mode `md2`, `N2` terms), `arctan T` (`mdm`, `Nm`). -/
structure GamD where
  T : Q
  k2 : ℤ
  n2 : ℕ
  km : ℤ
  nm : ℕ
  md2 : ℕ
  N2 : ℕ
  mdm : ℕ
  Nm : ℕ

namespace GamD

/-- `1 + T²/4`. -/
def v2 (G : GamD) : Q := add (ofNat 1) (div (npow G.T 2) (ofNat 4))

/-- `1/4 + T²/4`. -/
def vm (G : GamD) : Q := add (frac 1 4) (div (npow G.T 2) (ofNat 4))

/-- `T / 2`. -/
def half (G : GamD) : Q := div G.T (ofNat 2)

theorem val_v2 (G : GamD) : G.v2.val = 1 + G.T.val ^ 2 / 4 := by
  rw [v2, val_add, val_ofNat, val_div _ four_n_pos, val_npow, val_ofNat]; push_cast; ring

theorem val_vm (G : GamD) : G.vm.val = 1 / 4 + G.T.val ^ 2 / 4 := by
  rw [vm, val_add, val_frac _ (by norm_num), val_div _ four_n_pos, val_npow, val_ofNat]
  push_cast; ring

theorem val_half (G : GamD) : G.half.val = G.T.val / 2 := by
  rw [half, val_div _ two_n_pos, val_ofNat]; push_cast; ring

end GamD

/-- Admissibility of the height certificate. -/
def gamOK (G : GamD) : Bool :=
  le (ofNat 0) G.T && logOK G.v2 G.k2 && logOK G.vm G.km && atanOK G.half G.md2 && atanOK G.T G.mdm

/-- `S2 T ≥ 1/2 atanLo(T/2) + T/4 logLo(1 + T²/4) - T/2 - T/2 log π⁺`. -/
def S2lo (G : GamD) : Q :=
  sub (sub (add (mul (frac 1 2) (arctanLo G.half G.N2 G.md2)) (mul (div G.T (ofNat 4))
    (logLo G.v2 G.k2 G.n2))) (div G.T (ofNat 2))) (mul (div G.T (ofNat 2)) lphi)

def S2hi (G : GamD) : Q :=
  sub (sub (add (mul (frac 1 2) (arctanHi G.half G.N2 G.md2)) (mul (div G.T (ofNat 4))
    (logHi G.v2 G.k2 G.n2))) (div G.T (ofNat 2))) (mul (div G.T (ofNat 2)) lplo)

/-- `Sm1 T ≥ T/4 logLo(1/4 + T²/4) + atanLo T - T/2 - T/2 log π⁺`. -/
def Sm1lo (G : GamD) : Q :=
  sub (sub (add (mul (div G.T (ofNat 4)) (logLo G.vm G.km G.nm)) (arctanLo G.T G.Nm G.mdm))
    (div G.T (ofNat 2))) (mul (div G.T (ofNat 2)) lphi)

def Sm1hi (G : GamD) : Q :=
  sub (sub (add (mul (div G.T (ofNat 4)) (logHi G.vm G.km G.nm)) (arctanHi G.T G.Nm G.mdm))
    (div G.T (ofNat 2))) (mul (div G.T (ofNat 2)) lplo)

theorem S2_mem (G : GamD) (h : gamOK G = true) :
    (S2lo G).val ≤ ArgGammaR.S2 G.T.val ∧ ArgGammaR.S2 G.T.val ≤ (S2hi G).val := by
  simp only [gamOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hT, hl2⟩, _⟩, ha2⟩, _⟩ := h
  have hT' := le_sound hT
  rw [val_ofNat, Nat.cast_zero] at hT'
  have hl := log_mem G.v2 G.k2 G.n2 hl2
  rw [G.val_v2] at hl
  have ha := arctan_mem G.half G.N2 G.md2 ha2
  rw [G.val_half] at ha
  have hm := ArgGammaR.S2_mem_of hT' hl ha logpi_mem
  unfold S2lo S2hi
  simp only [val_sub, val_add, val_mul, val_div _ four_n_pos, val_div _ two_n_pos,
    val_frac 1 (by norm_num : 1 ≤ 2), val_ofNat]
  push_cast
  constructor <;> linarith [hm.1, hm.2]

theorem Sm1_mem (G : GamD) (h : gamOK G = true) :
    (Sm1lo G).val ≤ ArgGammaR.Sm1 G.T.val ∧ ArgGammaR.Sm1 G.T.val ≤ (Sm1hi G).val := by
  simp only [gamOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hT, _⟩, hlm⟩, _⟩, ham⟩ := h
  have hT' := le_sound hT
  rw [val_ofNat, Nat.cast_zero] at hT'
  have hl := log_mem G.vm G.km G.nm hlm
  rw [G.val_vm] at hl
  have ha := arctan_mem G.T G.Nm G.mdm ham
  have hm := ArgGammaR.Sm1_mem_of hT' hl ha logpi_mem
  unfold Sm1lo Sm1hi
  simp only [val_sub, val_add, val_mul, val_div _ four_n_pos, val_div _ two_n_pos, val_ofNat]
  push_cast
  constructor <;> linarith [hm.1, hm.2]

/-! ## E. The K6b comparisons of a band -/

/-- `em1 T = T / (2 (1 + T²))`. -/
def em1Q (T : Q) : Q := div T (mul (ofNat 2) (add (ofNat 1) (npow T 2)))

/-- `e2 T = T / (2 (4 + T²))`. -/
def e2Q (T : Q) : Q := div T (mul (ofNat 2) (add (ofNat 4) (npow T 2)))

theorem npow_two_nonneg_n (T : Q) : 0 ≤ (npow T 2).n := by
  show 0 ≤ 1 * T.n * T.n
  rw [one_mul]; exact mul_self_nonneg _

theorem val_em1Q (T : Q) : (em1Q T).val = ArgGammaR.em1 T.val := by
  have hpos : 0 < (mul (ofNat 2) (add (ofNat 1) (npow T 2))).n := by
    show 0 < ((2 : ℕ) : ℤ) * (((1 : ℕ) : ℤ) * ((npow T 2).dm + 1 : ℤ) + (npow T 2).n * ((0 : ℕ) + 1 : ℤ))
    have := npow_two_nonneg_n T
    positivity
  rw [em1Q, val_div _ hpos, val_mul, val_add, val_npow, val_ofNat, val_ofNat, ArgGammaR.em1]
  push_cast; ring

theorem val_e2Q (T : Q) : (e2Q T).val = ArgGammaR.e2 T.val := by
  have hpos : 0 < (mul (ofNat 2) (add (ofNat 4) (npow T 2))).n := by
    show 0 < ((2 : ℕ) : ℤ) * (((4 : ℕ) : ℤ) * ((npow T 2).dm + 1 : ℤ) + (npow T 2).n * ((0 : ℕ) + 1 : ℤ))
    have := npow_two_nonneg_n T
    positivity
  rw [e2Q, val_div _ hpos, val_mul, val_add, val_npow, val_ofNat, val_ofNat, ArgGammaR.e2]
  push_cast; ring

/-- **The K6b check of a band** with edge heights `G0.T ≤ G1.T`: `[L4, H4] ⊇` the `σ = -1` bracket,
    `[L5, H5] ⊇` the `σ = 2` bracket. -/
def k6B (G0 G1 : GamD) (L4 H4 L5 H5 : Q) : Bool :=
  gamOK G0 && gamOK G1 &&
    le L4 (sub (sub (Sm1lo G1) (Sm1hi G0)) (em1Q G1.T)) &&
    le (add (sub (Sm1hi G1) (Sm1lo G0)) (em1Q G0.T)) H4 &&
    le L5 (sub (sub (S2lo G1) (S2hi G0)) (e2Q G1.T)) &&
    le (add (sub (S2hi G1) (S2lo G0)) (e2Q G0.T)) H5

theorem k6B_sound (G0 G1 : GamD) (L4 H4 L5 H5 : Q) (h : k6B G0 G1 L4 H4 L5 H5 = true) :
    0 ≤ G0.T.val ∧ 0 ≤ G1.T.val ∧
      L4.val ≤ ArgGammaR.Sm1 G1.T.val - ArgGammaR.Sm1 G0.T.val - ArgGammaR.em1 G1.T.val ∧
      ArgGammaR.Sm1 G1.T.val - ArgGammaR.Sm1 G0.T.val + ArgGammaR.em1 G0.T.val ≤ H4.val ∧
      L5.val ≤ ArgGammaR.S2 G1.T.val - ArgGammaR.S2 G0.T.val - ArgGammaR.e2 G1.T.val ∧
      ArgGammaR.S2 G1.T.val - ArgGammaR.S2 G0.T.val + ArgGammaR.e2 G0.T.val ≤ H5.val := by
  simp only [k6B, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, hL4⟩, hH4⟩, hL5⟩, hH5⟩ := h
  have a0 := Sm1_mem G0 h0
  have a1 := Sm1_mem G1 h1
  have b0 := S2_mem G0 h0
  have b1 := S2_mem G1 h1
  have hT0 : 0 ≤ G0.T.val := by
    have := h0
    simp only [gamOK, Bool.and_eq_true] at this
    have h' := le_sound this.1.1.1.1
    rw [val_ofNat, Nat.cast_zero] at h'
    exact h'
  have hT1 : 0 ≤ G1.T.val := by
    have := h1
    simp only [gamOK, Bool.and_eq_true] at this
    have h' := le_sound this.1.1.1.1
    rw [val_ofNat, Nat.cast_zero] at h'
    exact h'
  have l4 := le_sound hL4
  have h4 := le_sound hH4
  have l5 := le_sound hL5
  have h5 := le_sound hH5
  rw [val_sub, val_sub, val_em1Q] at l4
  rw [val_add, val_sub, val_em1Q] at h4
  rw [val_sub, val_sub, val_e2Q] at l5
  rw [val_add, val_sub, val_e2Q] at h5
  refine ⟨hT0, hT1, ?_, ?_, ?_, ?_⟩ <;> linarith [a0.1, a0.2, a1.1, a1.2, b0.1, b0.2, b1.1, b1.2]

end Arb4
