/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/
import EMZetaOfflineEval
import Probes.ArbEconomics_Sound

open Real Finset

namespace ArbEcon

namespace Off

@[simp] theorem p_pow (a b : ℕ) : Nat.pow a b = a ^ b := rfl

/-! ## A. Specifications. -/

/-- `s = σ + i t`. -/
noncomputable def sOfG (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

/-- `Σ_{m=1}^{n} (log m)^k m^(-s)`. -/
noncomputable def psumK (σ t : ℝ) (k n : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ico 1 (n + 1), ((Real.log m : ℝ) : ℂ) ^ k * (m : ℂ) ^ (-sOfG σ t)

/-- A complex signed ball encloses `z`. -/
def AccOK (P : ℕ) (z : ℂ) (x : Acc) : Prop :=
  |z.re * 2 ^ P - ((x.reP : ℝ) - x.reN)| ≤ x.reR ∧ |z.im * 2 ^ P - ((x.imP : ℝ) - x.imN)| ≤ x.imR

/-- A term ball encloses `z`. -/
def TBOK (P : ℕ) (z : ℂ) (t : TB) : Prop :=
  |z.re * 2 ^ P - sgn t.rs * t.rm| ≤ t.rr ∧ |z.im * 2 ^ P - sgn t.is * t.im| ≤ t.ir

/-- The accumulator list encloses `f k, f (k+1), …`. -/
def AccsOK (P : ℕ) (f : ℕ → ℂ) : ℕ → List Acc → Prop
  | _, [] => True
  | k, x :: xs => AccOK P (f k) x ∧ AccsOK P f (k + 1) xs

/-- The loop invariant after `n` terms. -/
def InvO (c : Cfg) (σ t : ℝ) (n : ℕ) (s : StO) : Prop :=
  s.n = n ∧ 1 ≤ n ∧ (s.llo : ℝ) ≤ Real.log n * 2 ^ c.P ∧ Real.log n * 2 ^ c.P ≤ s.lhi ∧
    AccsOK c.P (fun k => psumK σ t k n) 0 s.acc

/-- Validity of an off-line configuration for `σ`. -/
structure OValid (c : Cfg) (o : OCfg) (σ : ℝ) : Prop where
  oneQ_eq : o.oneQ = 2 ^ (o.q * c.P)
  q_pos : 1 ≤ o.q
  sigma_eq : σ = ((o.a : ℝ) - o.b) / o.q

/-! ## B. The bracket-times-ball product. -/

theorem imul_sound (P lo hi vm vr : ℕ) (vs : Bool) (x v : ℝ) (hx0 : 0 ≤ x)
    (hlo : (lo : ℝ) ≤ x * 2 ^ P) (hhi : x * 2 ^ P ≤ hi) (hv : |v * 2 ^ P - sgn vs * vm| ≤ vr) :
    |x * v * 2 ^ P - sgn vs * (imC P hi vm : ℝ)| ≤ (imR P lo hi vm vr : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hle : lo ≤ hi := by exact_mod_cast le_trans hlo hhi
  obtain ⟨a1, a2⟩ := shr_bounds (hi * vm) P
  obtain ⟨_, b2⟩ := shr_bounds (hi * vr) P
  obtain ⟨_, c2⟩ := shr_bounds ((hi - lo) * vm) P
  have hsub : (((hi - lo : ℕ)) : ℝ) = (hi : ℝ) - lo := by rw [Nat.cast_sub hle]
  simp only [imC, imR, p_add, p_mul, p_sub, p_shr] at a1 a2 b2 c2 ⊢
  push_cast [hsub] at a1 a2 b2 c2 ⊢
  set T := (((hi * vm) >>> P : ℕ) : ℝ) with hT
  set U := (((hi * vr) >>> P : ℕ) : ℝ) with hU
  set V := ((((hi - lo) * vm) >>> P : ℕ) : ℝ) with hV
  have hvm0 : (0 : ℝ) ≤ vm := Nat.cast_nonneg vm
  have hvr0 : (0 : ℝ) ≤ vr := Nat.cast_nonneg vr
  have e : x * v * 2 ^ P - sgn vs * T
      = x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - hi) / 2 ^ P)
        + sgn vs * ((hi : ℝ) * vm / 2 ^ P - T) := by
    field_simp; ring
  rw [e]
  have t1 : |x * (v * 2 ^ P - sgn vs * vm)| ≤ (hi : ℝ) * vr / 2 ^ P := by
    rw [abs_mul, abs_of_nonneg hx0]
    have h1 : x * |v * 2 ^ P - sgn vs * vm| ≤ x * vr := mul_le_mul_of_nonneg_left hv hx0
    have h2 : x * (vr : ℝ) ≤ (hi : ℝ) * vr / 2 ^ P := by
      rw [le_div_iff₀ hP]; nlinarith
    linarith
  have t2 : |sgn vs * (vm * (x * 2 ^ P - hi) / 2 ^ P)| ≤ ((hi : ℝ) - lo) * vm / 2 ^ P := by
    rw [abs_mul, abs_sgn, one_mul, abs_div, abs_of_pos hP, abs_mul, abs_of_nonneg hvm0]
    apply div_le_div_of_nonneg_right _ hP.le
    have : |x * 2 ^ P - hi| ≤ (hi : ℝ) - lo := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (x * 2 ^ P - hi)]
  have t3 : |sgn vs * ((hi : ℝ) * vm / 2 ^ P - T)| ≤ 1 := by
    rw [abs_mul, abs_sgn, one_mul, abs_le]
    constructor <;> linarith
  have q1 := abs_add_le (x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - hi) / 2 ^ P))
    (sgn vs * ((hi : ℝ) * vm / 2 ^ P - T))
  have q2 := abs_add_le (x * (v * 2 ^ P - sgn vs * vm)) (sgn vs * (vm * (x * 2 ^ P - hi) / 2 ^ P))
  have e2 : ((hi : ℝ) - lo) * vm / 2 ^ P = ((hi : ℝ) - lo) * vm / 2 ^ P := rfl
  linarith

/-! ## C. Term balls, accumulation, the log chain. -/

theorem tbMul_sound (P lo hi : ℕ) (x : ℝ) (w : ℂ) (t : TB) (hx0 : 0 ≤ x)
    (hlo : (lo : ℝ) ≤ x * 2 ^ P) (hhi : x * 2 ^ P ≤ hi) (ht : TBOK P w t) :
    TBOK P ((x : ℂ) * w) (tbMul P lo hi t) := by
  obtain ⟨h1, h2⟩ := ht
  have hre : ((x : ℂ) * w).re = x * w.re := by simp [Complex.mul_re]
  have him : ((x : ℂ) * w).im = x * w.im := by simp [Complex.mul_im]
  refine ⟨?_, ?_⟩
  · rw [hre]; exact imul_sound P lo hi t.rm t.rr t.rs x w.re hx0 hlo hhi h1
  · rw [him]; exact imul_sound P lo hi t.im t.ir t.is x w.im hx0 hlo hhi h2

theorem accAdd_sound (P : ℕ) (z w : ℂ) (x : Acc) (t : TB) (hx : AccOK P z x) (ht : TBOK P w t) :
    AccOK P (z + w) (accAdd x t) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨ht1, ht2⟩ := ht
  constructor
  · have hc : ((accAdd x t).reP : ℝ) - (accAdd x t).reN = ((x.reP : ℝ) - x.reN) + sgn t.rs * t.rm := by
      show ((Bool.rec x.reP (Nat.add x.reP t.rm) t.rs : ℕ) : ℝ)
        - ((Bool.rec (Nat.add x.reN t.rm) x.reN t.rs : ℕ) : ℝ) = _
      cases t.rs <;> simp [sgn] <;> ring
    have hr : ((accAdd x t).reR : ℝ) = x.reR + t.rr := by
      show ((Nat.add x.reR t.rr : ℕ) : ℝ) = _; simp
    rw [hc, hr, Complex.add_re]
    have e : (z.re + w.re) * 2 ^ P - (((x.reP : ℝ) - x.reN) + sgn t.rs * t.rm)
        = (z.re * 2 ^ P - ((x.reP : ℝ) - x.reN)) + (w.re * 2 ^ P - sgn t.rs * t.rm) := by ring
    rw [e]; exact le_trans (abs_add_le _ _) (add_le_add hx1 ht1)
  · have hc : ((accAdd x t).imP : ℝ) - (accAdd x t).imN = ((x.imP : ℝ) - x.imN) + sgn t.is * t.im := by
      show ((Bool.rec x.imP (Nat.add x.imP t.im) t.is : ℕ) : ℝ)
        - ((Bool.rec (Nat.add x.imN t.im) x.imN t.is : ℕ) : ℝ) = _
      cases t.is <;> simp [sgn] <;> ring
    have hr : ((accAdd x t).imR : ℝ) = x.imR + t.ir := by
      show ((Nat.add x.imR t.ir : ℕ) : ℝ) = _; simp
    rw [hc, hr, Complex.add_im]
    have e : (z.im + w.im) * 2 ^ P - (((x.imP : ℝ) - x.imN) + sgn t.is * t.im)
        = (z.im * 2 ^ P - ((x.imP : ℝ) - x.imN)) + (w.im * 2 ^ P - sgn t.is * t.im) := by ring
    rw [e]; exact le_trans (abs_add_le _ _) (add_le_add hx2 ht2)

theorem addChain_sound (P lo hi : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hlo : (lo : ℝ) ≤ x * 2 ^ P)
    (hhi : x * 2 ^ P ≤ hi) (f : ℕ → ℂ) (w : ℂ) :
    ∀ (xs : List Acc) (k : ℕ) (t : TB), TBOK P ((x : ℂ) ^ k * w) t → AccsOK P f k xs →
      AccsOK P (fun j => f j + (x : ℂ) ^ j * w) k (addChain P lo hi xs t) := by
  intro xs
  induction xs with
  | nil => intro k t _ _; trivial
  | cons a as ih =>
    intro k t ht hA
    obtain ⟨hA1, hA2⟩ := hA
    have hstep : addChain P lo hi (a :: as) t = accAdd a t :: addChain P lo hi as (tbMul P lo hi t) :=
      rfl
    rw [hstep]
    refine ⟨accAdd_sound P (f k) ((x : ℂ) ^ k * w) a t hA1 ht, ?_⟩
    apply ih (k + 1) (tbMul P lo hi t) _ hA2
    have := tbMul_sound P lo hi x ((x : ℂ) ^ k * w) t hx0 hlo hhi ht
    have e : (x : ℂ) * ((x : ℂ) ^ k * w) = (x : ℂ) ^ (k + 1) * w := by ring
    rw [e] at this
    exact this

/-! ## D. The validated amplitude bracket. -/

theorem rpow_neg_sigma_pow (m : ℕ) (hm : 1 ≤ m) (a b q : ℕ) (hq : 1 ≤ q) :
    ((m : ℝ) ^ (-(((a : ℝ) - b) / q))) ^ q * (m : ℝ) ^ a = (m : ℝ) ^ b := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [← Real.rpow_natCast ((m : ℝ) ^ _), ← Real.rpow_mul hmpos.le]
  have e : -(((a : ℝ) - b) / q) * (q : ℝ) = (b : ℝ) - a := by field_simp; ring
  rw [e, Real.rpow_sub hmpos, Real.rpow_natCast, Real.rpow_natCast]
  have : (0 : ℝ) < (m : ℝ) ^ a := by positivity
  field_simp

theorem ampl_sound (c : Cfg) (o : OCfg) (hone : c.one = 2 ^ c.P) (hQ : o.oneQ = 2 ^ (o.q * c.P))
    (hq : 1 ≤ o.q) (m gprev : ℕ) (hm : 1 ≤ m) :
    ((ampl c o m gprev).2.1 : ℝ) ≤ (m : ℝ) ^ (-(((o.a : ℝ) - o.b) / o.q)) * 2 ^ c.P ∧
    (m : ℝ) ^ (-(((o.a : ℝ) - o.b) / o.q)) * 2 ^ c.P ≤ ((ampl c o m gprev).2.2 : ℝ) := by
  set X : ℝ := (m : ℝ) ^ (-(((o.a : ℝ) - o.b) / o.q)) with hX
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hX0 : 0 < X := Real.rpow_pos_of_pos hmpos _
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  set Y : ℝ := X * 2 ^ c.P with hY
  have hY0 : 0 ≤ Y := by positivity
  have hma : (0 : ℝ) < (m : ℝ) ^ o.a := by positivity
  have hq0 : o.q ≠ 0 := by omega
  -- the key identity  Y^q m^a = 2^(qP) m^b
  have hkey : Y ^ o.q * (m : ℝ) ^ o.a = (2 : ℝ) ^ (o.q * c.P) * (m : ℝ) ^ o.b := by
    have h1 := rpow_neg_sigma_pow m hm o.a o.b o.q hq
    rw [← hX] at h1
    calc Y ^ o.q * (m : ℝ) ^ o.a = (X ^ o.q * (m : ℝ) ^ o.a) * ((2 : ℝ) ^ c.P) ^ o.q := by
          rw [hY, mul_pow]; ring
      _ = (m : ℝ) ^ o.b * (2 : ℝ) ^ (o.q * c.P) := by rw [h1, ← pow_mul, mul_comm c.P o.q]
      _ = (2 : ℝ) ^ (o.q * c.P) * (m : ℝ) ^ o.b := by ring
  set g := rootLoop o.q (Nat.mul o.oneQ (Nat.pow m o.b)) (Nat.pow m o.a) o.nfuel
    (Nat.add (Nat.add gprev (Nat.div gprev (Nat.sub m 1))) 2) with hg
  have hlo_eq : (ampl c o m gprev).2.1 = Bool.rec 0 g
      (Nat.ble (Nat.mul (Nat.pow g o.q) (Nat.pow m o.a)) (Nat.mul o.oneQ (Nat.pow m o.b))) := rfl
  have hhi_eq : (ampl c o m gprev).2.2 = Bool.rec (Nat.mul c.one (Nat.pow m o.b)) (Nat.succ g)
      (Nat.ble (Nat.mul o.oneQ (Nat.pow m o.b)) (Nat.mul (Nat.pow (Nat.succ g) o.q) (Nat.pow m o.a))) :=
    rfl
  constructor
  · rw [hlo_eq]
    cases hb : Nat.ble (Nat.mul (Nat.pow g o.q) (Nat.pow m o.a)) (Nat.mul o.oneQ (Nat.pow m o.b)) with
    | false => simp only; push_cast; exact hY0
    | true =>
      simp only
      have hle := Nat.le_of_ble_eq_true hb
      simp only [p_mul, p_pow] at hle
      have hleR : (g : ℝ) ^ o.q * (m : ℝ) ^ o.a ≤ (2 : ℝ) ^ (o.q * c.P) * (m : ℝ) ^ o.b := by
        have := (Nat.cast_le (α := ℝ)).mpr hle
        rw [hQ] at this; push_cast at this; exact this
      rw [← hkey] at hleR
      have hgq : (g : ℝ) ^ o.q ≤ Y ^ o.q := le_of_mul_le_mul_right hleR hma
      exact le_of_pow_le_pow_left₀ hq0 hY0 hgq
  · rw [hhi_eq]
    cases hb : Nat.ble (Nat.mul o.oneQ (Nat.pow m o.b)) (Nat.mul (Nat.pow (Nat.succ g) o.q) (Nat.pow m o.a)) with
    | false =>
      simp only
      -- fallback: m^(-σ) ≤ m^b
      have hexp : -(((o.a : ℝ) - o.b) / o.q) ≤ (o.b : ℝ) := by
        have hqR : (1 : ℝ) ≤ o.q := by exact_mod_cast hq
        have ha0 : (0 : ℝ) ≤ o.a := Nat.cast_nonneg _
        have hb0 : (0 : ℝ) ≤ o.b := Nat.cast_nonneg _
        rw [neg_div', div_le_iff₀ (by linarith)]
        nlinarith
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hXle : X ≤ (m : ℝ) ^ o.b := by
        rw [hX, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hm1 hexp
      rw [hone]; simp only [p_mul, p_pow]; push_cast
      rw [hY]; nlinarith
    | true =>
      simp only
      have hle := Nat.le_of_ble_eq_true hb
      simp only [p_mul, p_pow] at hle
      have hleR : (2 : ℝ) ^ (o.q * c.P) * (m : ℝ) ^ o.b ≤ ((g : ℝ) + 1) ^ o.q * (m : ℝ) ^ o.a := by
        have := (Nat.cast_le (α := ℝ)).mpr hle
        rw [hQ] at this; push_cast at this; exact this
      rw [← hkey] at hleR
      have hgq : Y ^ o.q ≤ ((g : ℝ) + 1) ^ o.q := le_of_mul_le_mul_right hleR hma
      have := le_of_pow_le_pow_left₀ hq0 (by positivity) hgq
      push_cast
      exact this

/-! ## E. The term `m^(-s)`. -/

theorem cpow_termG (m : ℕ) (hm : 0 < m) (σ t : ℝ) :
    ((m : ℂ) ^ (-sOfG σ t)).re = (m : ℝ) ^ (-σ) * Real.cos (t * Real.log m) ∧
    ((m : ℂ) ^ (-sOfG σ t)).im = -((m : ℝ) ^ (-σ) * Real.sin (t * Real.log m)) := by
  have hnpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlog : Complex.log (m : ℂ) = (Real.log m : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le]
  have hre : (((Real.log m : ℝ) : ℂ) * -sOfG σ t).re = -σ * Real.log m := by
    simp only [sOfG, Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.neg_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have him : (((Real.log m : ℝ) : ℂ) * -sOfG σ t).im = -(t * Real.log m) := by
    simp only [sOfG, Complex.mul_im, Complex.neg_re, Complex.add_re, Complex.neg_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    ring
  have hrp : Real.exp (-σ * Real.log m) = (m : ℝ) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hnpos]; ring_nf
  rw [Complex.cpow_def_of_ne_zero hne, hlog]
  constructor
  · rw [Complex.exp_re, hre, him, Real.cos_neg, hrp]
  · rw [Complex.exp_im, hre, him, Real.sin_neg, hrp]; ring

theorem termTB_sound (P Xlo Xhi : ℕ) (tr : Trig) (m : ℕ) (hm : 0 < m) (σ t : ℝ)
    (hXlo : (Xlo : ℝ) ≤ (m : ℝ) ^ (-σ) * 2 ^ P) (hXhi : (m : ℝ) ^ (-σ) * 2 ^ P ≤ Xhi)
    (htr : TrigOK P (t * Real.log m) tr) :
    TBOK P ((m : ℂ) ^ (-sOfG σ t)) (termTB P Xlo Xhi tr) := by
  obtain ⟨hc, hs, _, _⟩ := htr
  obtain ⟨ere, eim⟩ := cpow_termG m hm σ t
  have hX0 : (0 : ℝ) ≤ (m : ℝ) ^ (-σ) := by positivity
  constructor
  · rw [ere]
    exact imul_sound P Xlo Xhi tr.cm tr.cr tr.cs _ _ hX0 hXlo hXhi hc
  · rw [eim]
    have h := imul_sound P Xlo Xhi tr.sm tr.sr tr.ss _ _ hX0 hXlo hXhi hs
    show |-((m : ℝ) ^ (-σ) * Real.sin (t * Real.log m)) * 2 ^ P - sgn (!tr.ss) * (imC P Xhi tr.sm : ℝ)|
      ≤ (imR P Xlo Xhi tr.sm tr.sr : ℝ)
    rw [sgn_not]
    have e : -((m : ℝ) ^ (-σ) * Real.sin (t * Real.log m)) * 2 ^ P - -sgn tr.ss * (imC P Xhi tr.sm : ℝ)
        = -((m : ℝ) ^ (-σ) * Real.sin (t * Real.log m) * 2 ^ P - sgn tr.ss * (imC P Xhi tr.sm : ℝ)) := by
      ring
    rw [e, abs_neg]; exact h

/-! ## F. The partial sums. -/

theorem psumK_succ (σ t : ℝ) (k n : ℕ) :
    psumK σ t k (n + 1) = psumK σ t k n
      + ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ k * (((n + 1 : ℕ) : ℕ) : ℂ) ^ (-sOfG σ t) := by
  simp only [psumK]
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]

theorem psumK_one_zero (σ t : ℝ) : psumK σ t 0 1 = 1 := by
  simp [psumK]

theorem psumK_one_succ (σ t : ℝ) (k : ℕ) : psumK σ t (k + 1) 1 = 0 := by
  simp [psumK]

/-! ## G. One step, the run, the chunks. -/

theorem stepO_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (K : ℕ) (hv : Valid c t K)
    (ho : OValid c o σ) (n : ℕ) (s : StO) (hI : InvO c σ t n s) :
    InvO c σ t (n + 1) (stepO c o s) := by
  obtain ⟨hn, h1, hllo, hlhi, hacc⟩ := hI
  subst hn
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have hm2 : 2 ≤ s.n + 1 := by omega
  have hmpos : 0 < s.n + 1 := by omega
  -- the log bracket (same computation as `ArbEcon.step`)
  have hls := logInc_spec c t K hv (s.n + 1)
  obtain ⟨lb1, lb2⟩ := logInc_bound c.P (s.n + 1) hm2 (logInc c (s.n + 1)) hls
  have hmn : ((s.n + 1 : ℕ) : ℝ) - 1 = (s.n : ℝ) := by push_cast; ring
  rw [hmn] at lb1 lb2
  have hllo' : ((stepO c o s).llo : ℝ) = s.llo + (logInc c (s.n + 1)).1 := by
    show ((Nat.add s.llo (logInc c (Nat.succ s.n)).1 : ℕ) : ℝ) = _
    simp only [p_add]; push_cast; rfl
  have hlhi' : ((stepO c o s).lhi : ℝ) = s.lhi + (logInc c (s.n + 1)).1 + (logInc c (s.n + 1)).2.1
      + ((2 ^ (c.P + 1) / (logInc c (s.n + 1)).2.2 : ℕ) + 1) := by
    show ((Nat.add (Nat.add (Nat.add s.lhi (logInc c (Nat.succ s.n)).1) (logInc c (Nat.succ s.n)).2.1)
      (Nat.add (Nat.div c.two1 (logInc c (Nat.succ s.n)).2.2) 1) : ℕ) : ℝ) = _
    rw [hv.two1_eq]; simp only [p_add, p_div]; push_cast; rfl
  have hLlo : ((stepO c o s).llo : ℝ) ≤ Real.log ((s.n + 1 : ℕ) : ℝ) * 2 ^ c.P := by
    rw [hllo']; nlinarith [lb1, hllo]
  have hLhi : Real.log ((s.n + 1 : ℕ) : ℝ) * 2 ^ c.P ≤ (stepO c o s).lhi := by
    rw [hlhi']; nlinarith [lb2, hlhi]
  -- the amplitude
  have ham := ampl_sound c o hv.one_eq ho.oneQ_eq ho.q_pos (s.n + 1) s.g (by omega)
  rw [← ho.sigma_eq] at ham
  -- theta and trig
  have htb := theta_bracket c.P c.tn c.tq (Real.log ((s.n + 1 : ℕ) : ℝ)) (stepO c o s).llo
    (stepO c o s).lhi hLlo hLhi
  rw [← hv.t_eq] at htb
  have htr := trig_sound c t K hv (t * Real.log ((s.n + 1 : ℕ) : ℝ)) _ _ htb.1 htb.2
  have hterm := termTB_sound c.P (ampl c o (s.n + 1) s.g).2.1 (ampl c o (s.n + 1) s.g).2.2 _
    (s.n + 1) hmpos σ t ham.1 ham.2 htr
  -- the chain
  have hlog0 : (0 : ℝ) ≤ Real.log ((s.n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ s.n + 1 by omega))
  have hterm0 : TBOK c.P (((Real.log ((s.n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ 0 * (((s.n + 1 : ℕ) : ℂ)) ^ (-sOfG σ t))
      (termTB c.P (ampl c o (s.n + 1) s.g).2.1 (ampl c o (s.n + 1) s.g).2.2
        (trig c (Nat.shiftRight (Nat.mul c.tn (stepO c o s).llo) c.tq)
          (Nat.add (Nat.shiftRight (Nat.mul c.tn (stepO c o s).lhi) c.tq) 1))) := by
    rw [pow_zero, one_mul]; exact hterm
  have hchain := addChain_sound c.P (stepO c o s).llo (stepO c o s).lhi
    (Real.log ((s.n + 1 : ℕ) : ℝ)) hlog0 hLlo hLhi
    (fun k => psumK σ t k s.n) ((((s.n + 1 : ℕ) : ℂ)) ^ (-sOfG σ t)) s.acc 0 _ hterm0 hacc
  refine ⟨rfl, by omega, hLlo, hLhi, ?_⟩
  have hf : (fun k => psumK σ t k (s.n + 1))
      = (fun k => psumK σ t k s.n
          + ((Real.log ((s.n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ k * (((s.n + 1 : ℕ) : ℂ)) ^ (-sOfG σ t)) := by
    funext k; rw [psumK_succ]
  rw [hf]
  exact hchain

theorem runO_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (K : ℕ) (hv : Valid c t K) (ho : OValid c o σ) :
    ∀ (L n : ℕ) (s : StO), InvO c σ t n s → InvO c σ t (n + L) (runO c o L s) := by
  intro L
  induction L with
  | zero => intro n s h; exact h
  | succ L ih =>
    intro n s h
    have := ih (n + 1) (stepO c o s) (stepO_sound c o σ t K hv ho n s h)
    rw [show n + (L + 1) = n + 1 + L by ring]
    exact this

theorem Acc.beq_eq (x y : Acc) (h : Acc.beq x y = true) : x = y := by
  obtain ⟨_, _, _, _, _, _⟩ := x
  obtain ⟨_, _, _, _, _, _⟩ := y
  simp only [Acc.beq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6]

theorem accsBeq_eq : ∀ (xs ys : List Acc), accsBeq xs ys = true → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys => exact absurd h (by simp [accsBeq])
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => exact absurd h (by simp [accsBeq])
    | cons y ys =>
      have h' : (Acc.beq x y && accsBeq xs ys) = true := h
      rw [Bool.and_eq_true] at h'
      rw [Acc.beq_eq x y h'.1, ih ys h'.2]

theorem StO.beq_eq (x y : StO) (h : StO.beq x y = true) : x = y := by
  obtain ⟨_, _, _, _, _⟩ := x
  obtain ⟨_, _, _, _, _⟩ := y
  simp only [StO.beq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, accsBeq_eq _ _ h5]

/-- **Chunk composition.**  A kernel-checked chunk `StO.beq (runO c o L s) s' = true` transports the
    invariant from `s` (after `n` terms) to `s'` (after `n + L` terms). -/
theorem chunkO_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (K : ℕ) (hv : Valid c t K) (ho : OValid c o σ)
    (L n : ℕ) (s s' : StO) (hI : InvO c σ t n s) (hchk : StO.beq (runO c o L s) s' = true) :
    InvO c σ t (n + L) s' := by
  rw [← StO.beq_eq _ _ hchk]; exact runO_sound c o σ t K hv ho L n s hI

theorem accsOK_zero (P : ℕ) (f : ℕ → ℂ) :
    ∀ (p k : ℕ), (∀ j, k ≤ j → f j = 0) → AccsOK P f k (List.replicate p Acc.zero) := by
  intro p
  induction p with
  | zero => intro k _; trivial
  | succ p ih =>
    intro k hf
    refine ⟨?_, ih (k + 1) (fun j hj => hf j (by omega))⟩
    rw [hf k le_rfl]
    simp [AccOK, Acc.zero]

/-- The initial state encloses the partial sums after `n = 1`. -/
theorem initO_sound (c : Cfg) (σ t : ℝ) (p : ℕ) (hone : c.one = 2 ^ c.P) :
    InvO c σ t 1 (StO.init c p) := by
  refine ⟨rfl, le_rfl, ?_, ?_, ?_⟩
  · simp [StO.init]
  · simp [StO.init]
  · refine ⟨?_, ?_⟩
    · show AccOK c.P (psumK σ t 0 1) _
      rw [psumK_one_zero]
      simp [AccOK, hone]
    · apply accsOK_zero
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact psumK_one_succ σ t j'

end Off

end ArbEcon
