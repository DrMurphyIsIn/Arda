/-  SpeiserDerivCore.lean -- a KERNEL checker for zero-free cells of `deriv riemannZeta`
    (MM_speiser_box_probe, the Face-7 pilot box; 2026-10-15).

    The zero-free cells of `EMZetaOfflineSlab*` freeze the Euler-Maclaurin correction factor
    `emCorr K s N` at the cell centre and pay its variation (`corrVar`, about `3 N r / t²`).  That
    error is LINEAR in the radius, so a Cauchy estimate turns it into an O(1) error on `ζ'`:
    useless at the heights `6 ≤ t ≤ 10` of the pilot box.  This file replaces the frozen factor by
    its exact expansion and certifies `ζ' ≠ 0` on a disc:

      * `GQ`, `peval`, `padd`, `pmul`, `pderiv` -- Gaussian-rational polynomials (computable) and
        their complex evaluation, product and derivative laws;
      * `emCorr_expand`   -- `emCorr K (c + h) N` is EXACTLY the polynomial `gammaList c N K J`
                             in `h` plus a geometric tail `N (-h/(c-1))^(J+1) / (c - 1 + h)`;
      * `model_err`       -- the order-`p` Taylor model of the finite EM part, with the expanded
                             correction factor, is uniformly close to `emFinite` on the disc;
      * `em_remainder_region0` -- the order-(2K+1) EM remainder bound for `0 ≤ Re s ≤ 1`;
      * `checkD`, `cell_deriv_ne_zero` -- ONE Boolean check (run by `decide +kernel`) on the
        evaluator's accumulators, and its soundness: the model polynomial `M` with exact
        Gaussian-rational coefficients satisfies `sup_{‖z - c‖ ≤ r + ρ} ‖ζ z - M(z - c)‖ ≤ F ρ`
        and `‖M'(h)‖ > F` for `‖h‖ ≤ r`; by Cauchy's estimate on the circle of radius `ρ`,
        `‖ζ'(s) - M'(s - c)‖ ≤ F`, hence `ζ'(s) ≠ 0` for every `s` with `‖s - c‖ ≤ r`.

    NOT the Speiser wall.  Speiser (1935): `ζ'` zero-free on the WHOLE open left strip
    `0 < Re s < 1/2` is equivalent to RH; finitely many discs decide nothing about RH.
    conjecture1_proved = False.
-/
import EMZetaOfflineSlabCheck
import Mathlib.Analysis.Complex.Liouville

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon.Off.SpD

/-! ## A. Gaussian rationals. -/

/-- A Gaussian rational `re + i im`. -/
structure GQ where
  re : ℚ
  im : ℚ

namespace GQ

def zero : GQ := ⟨0, 0⟩
def ofQ (q : ℚ) : GQ := ⟨q, 0⟩
def add (a b : GQ) : GQ := ⟨a.re + b.re, a.im + b.im⟩
def neg (a : GQ) : GQ := ⟨-a.re, -a.im⟩
def mul (a b : GQ) : GQ := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def nsq (a : GQ) : ℚ := a.re * a.re + a.im * a.im
def inv (a : GQ) : GQ := ⟨a.re / a.nsq, -a.im / a.nsq⟩
/-- The `ℓ¹` size `|re| + |im|`, an upper bound of the modulus. -/
def l1 (a : GQ) : ℚ := |a.re| + |a.im|

/-- The complex number. -/
noncomputable def toC (a : GQ) : ℂ := ((a.re : ℝ) : ℂ) + ((a.im : ℝ) : ℂ) * I

@[simp] theorem toC_re (a : GQ) : (toC a).re = (a.re : ℝ) := by simp [toC]
@[simp] theorem toC_im (a : GQ) : (toC a).im = (a.im : ℝ) := by simp [toC]

theorem toC_zero : toC zero = 0 := by apply Complex.ext <;> simp [zero]
theorem toC_ofQ (q : ℚ) : toC (ofQ q) = ((q : ℝ) : ℂ) := by apply Complex.ext <;> simp [ofQ]
theorem toC_add (a b : GQ) : toC (add a b) = toC a + toC b := by apply Complex.ext <;> simp [add]
theorem toC_neg (a : GQ) : toC (neg a) = -toC a := by apply Complex.ext <;> simp [neg]
theorem toC_mul (a b : GQ) : toC (mul a b) = toC a * toC b := by apply Complex.ext <;> simp [mul]

theorem normSq_toC (a : GQ) : Complex.normSq (toC a) = (a.nsq : ℝ) := by
  rw [Complex.normSq_apply]; simp [nsq]

theorem toC_inv (a : GQ) (h : a.nsq ≠ 0) : toC (inv a) = (toC a)⁻¹ := by
  have hR : ((a.nsq : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h
  apply Complex.ext
  · rw [Complex.inv_re, normSq_toC]; simp [inv]
  · rw [Complex.inv_im, normSq_toC]; simp [inv, neg_div]

theorem norm_toC_le (a : GQ) : ‖toC a‖ ≤ (a.l1 : ℝ) := by
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) (le_of_eq ?_)
  simp [l1]

theorem norm_toC_sq (a : GQ) : ‖toC a‖ ^ 2 = (a.nsq : ℝ) := by
  rw [Complex.sq_norm, normSq_toC]

end GQ

open GQ

/-! ## B. Polynomials over `GQ`, in Horner form `a₀ + h (a₁ + h (…))`. -/

/-- Complex evaluation. -/
noncomputable def peval : List GQ → ℂ → ℂ
  | [], _ => 0
  | a :: P, h => toC a + h * peval P h

def padd : List GQ → List GQ → List GQ
  | [], Q => Q
  | a :: P, [] => a :: P
  | a :: P, b :: Q => add a b :: padd P Q

def pscale (a : GQ) : List GQ → List GQ
  | [] => []
  | b :: Q => mul a b :: pscale a Q

def pmul : List GQ → List GQ → List GQ
  | [], _ => []
  | a :: P, Q => padd (pscale a Q) (zero :: pmul P Q)

/-- The derivative: `(a + h Q)' = Q + h Q'`. -/
def pderiv : List GQ → List GQ
  | [] => []
  | _ :: Q => padd Q (zero :: pderiv Q)

theorem peval_padd : ∀ (P Q : List GQ) (h : ℂ), peval (padd P Q) h = peval P h + peval Q h
  | [], Q, h => by simp [padd, peval]
  | a :: P, [], h => by simp [padd, peval]
  | a :: P, b :: Q, h => by
      simp only [padd, peval, toC_add, peval_padd P Q h]; ring

theorem peval_pscale (a : GQ) : ∀ (Q : List GQ) (h : ℂ), peval (pscale a Q) h = toC a * peval Q h
  | [], h => by simp [pscale, peval]
  | b :: Q, h => by
      simp only [pscale, peval, toC_mul, peval_pscale a Q h]; ring

theorem peval_pmul : ∀ (P Q : List GQ) (h : ℂ), peval (pmul P Q) h = peval P h * peval Q h
  | [], Q, h => by simp [pmul, peval]
  | a :: P, Q, h => by
      simp only [pmul, peval_padd, peval_pscale, peval, toC_zero, peval_pmul P Q h]; ring

theorem hasDerivAt_peval : ∀ (P : List GQ) (h : ℂ),
    HasDerivAt (fun z => peval P z) (peval (pderiv P) h) h
  | [], h => by
      show HasDerivAt (fun _ => (0 : ℂ)) 0 h
      exact hasDerivAt_const h 0
  | a :: Q, h => by
      have ih := hasDerivAt_peval Q h
      have e : peval (pderiv (a :: Q)) h = 0 + (1 * peval Q h + h * peval (pderiv Q) h) := by
        simp only [pderiv, peval_padd, peval, toC_zero]; ring
      rw [e]
      exact (hasDerivAt_const h (toC a)).add ((hasDerivAt_id' h).mul ih)

/-- `Σ_i ‖a_i‖₁ r^i`, an upper bound of `‖P(h)‖` for `‖h‖ ≤ r`. -/
def pnub (r : ℚ) : List GQ → ℚ
  | [] => 0
  | a :: P => l1 a + r * pnub r P

theorem norm_peval_le (r : ℚ) (hr : 0 ≤ r) (h : ℂ) (hh : ‖h‖ ≤ (r : ℝ)) :
    ∀ P : List GQ, ‖peval P h‖ ≤ (pnub r P : ℝ)
  | [] => by simp [peval, pnub]
  | a :: P => by
      have ih := norm_peval_le r hr h hh P
      have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      simp only [peval, pnub, Rat.cast_add, Rat.cast_mul]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      exact add_le_add (norm_toC_le a) (mul_le_mul hh ih (norm_nonneg _) hr')

theorem norm_peval_cons_ge (r : ℚ) (hr : 0 ≤ r) (h : ℂ) (hh : ‖h‖ ≤ (r : ℝ)) (a : GQ)
    (P : List GQ) : ‖toC a‖ - (r : ℝ) * (pnub r P : ℝ) ≤ ‖peval (a :: P) h‖ := by
  have ih := norm_peval_le r hr h hh P
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : ‖h * peval P h‖ ≤ (r : ℝ) * (pnub r P : ℝ) := by
    rw [norm_mul]; exact mul_le_mul hh ih (norm_nonneg _) hr'
  have h2 := norm_sub_norm_le (toC a) (-(h * peval P h))
  rw [sub_neg_eq_add, norm_neg] at h2
  show ‖toC a‖ - (r : ℝ) * (pnub r P : ℝ) ≤ ‖toC a + h * peval P h‖
  linarith

/-! ## C. Complex coefficient lists (the TRUE model) and their evaluation. -/

noncomputable def cpeval : List ℂ → ℂ → ℂ
  | [], _ => 0
  | a :: P, h => a + h * cpeval P h

noncomputable def cList (f : ℕ → ℂ) : ℕ → ℕ → List ℂ
  | _, 0 => []
  | k, n + 1 => f k :: cList f (k + 1) n

theorem cList_length (f : ℕ → ℂ) : ∀ n k, (cList f k n).length = n
  | 0, _ => rfl
  | n + 1, k => by simp [cList, cList_length f n (k + 1)]

theorem cpeval_cList (f : ℕ → ℂ) (h : ℂ) :
    ∀ n k, cpeval (cList f k n) h = ∑ i ∈ Finset.range n, f (k + i) * h ^ i
  | 0, k => by simp [cList, cpeval]
  | n + 1, k => by
      rw [Finset.sum_range_succ']
      simp only [cList, cpeval, cpeval_cList f h n (k + 1), Finset.mul_sum, add_zero, pow_zero,
        mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show k + (i + 1) = k + 1 + i by omega, pow_succ]
      ring

/-! ## D. From evaluator accumulators to Gaussian rationals. -/

/-- The centre of an accumulator ball. -/
def accQ (P : ℕ) (x : Acc) : GQ := ⟨((x.reP : ℚ) - x.reN) / 2 ^ P, ((x.imP : ℚ) - x.imN) / 2 ^ P⟩

/-- Its `ℓ¹` radius. -/
def accRad (P : ℕ) (x : Acc) : ℚ := ((x.reR : ℚ) + x.imR) / 2 ^ P

theorem accQ_close (P : ℕ) (z : ℂ) (x : Acc) (hx : AccOK P z x) :
    ‖z - toC (accQ P x)‖ ≤ (accRad P x : ℝ) := by
  obtain ⟨h1, h2⟩ := hx
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  have e1 : (z - toC (accQ P x)).re = (z.re * 2 ^ P - ((x.reP : ℝ) - x.reN)) / 2 ^ P := by
    simp only [Complex.sub_re, toC_re, accQ]
    push_cast
    field_simp
  have e2 : (z - toC (accQ P x)).im = (z.im * 2 ^ P - ((x.imP : ℝ) - x.imN)) / 2 ^ P := by
    simp only [Complex.sub_im, toC_im, accQ]
    push_cast
    field_simp
  rw [e1, e2, abs_div, abs_div, abs_of_pos hP]
  simp only [accRad]
  push_cast
  rw [add_div]
  exact add_le_add (div_le_div_of_nonneg_right h1 hP.le) (div_le_div_of_nonneg_right h2 hP.le)

/-- The ball of a difference of two accumulators. -/
def accSub (x2 x1 : Acc) : Acc :=
  ⟨x2.reP + x1.reN, x2.reN + x1.reP, x2.reR + x1.reR, x2.imP + x1.imN, x2.imN + x1.imP,
   x2.imR + x1.imR⟩

theorem accSub_ok (P : ℕ) (z2 z1 : ℂ) (x2 x1 : Acc) (h2 : AccOK P z2 x2) (h1 : AccOK P z1 x1) :
    AccOK P (z2 - z1) (accSub x2 x1) := by
  obtain ⟨a2, b2⟩ := h2
  obtain ⟨a1, b1⟩ := h1
  rw [abs_le] at a2 b2 a1 b1
  refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> simp only [accSub, Complex.sub_re, Complex.sub_im] <;>
    push_cast <;> constructor <;> nlinarith [a2.1, a2.2, b2.1, b2.2, a1.1, a1.2, b1.1, b1.2]

def accsSub : List Acc → List Acc → List Acc
  | x2 :: xs2, x1 :: xs1 => accSub x2 x1 :: accsSub xs2 xs1
  | _, _ => []

theorem accsSub_ok (P : ℕ) (f2 f1 : ℕ → ℂ) :
    ∀ (xs2 xs1 : List Acc) (k : ℕ), AccsOK P f2 k xs2 → AccsOK P f1 k xs1 →
      AccsOK P (fun j => f2 j - f1 j) k (accsSub xs2 xs1)
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, _, _ => trivial
  | x2 :: xs2, x1 :: xs1, k, h2, h1 =>
      ⟨accSub_ok P _ _ x2 x1 h2.1 h1.1, accsSub_ok P f2 f1 xs2 xs1 (k + 1) h2.2 h1.2⟩

theorem accsSub_length : ∀ (xs2 xs1 : List Acc) (n : ℕ), xs2.length = n → xs1.length = n →
    (accsSub xs2 xs1).length = n
  | [], [], _, h2, _ => by simpa [accsSub] using h2
  | [], _ :: _, n, h2, h1 => by simp at h2; subst h2; simp at h1
  | _ :: _, [], n, h2, h1 => by simp at h1; subst h1; simp at h2
  | x2 :: xs2, x1 :: xs1, n, h2, h1 => by
      simp only [List.length_cons] at h2 h1
      simp only [accsSub, List.length_cons]
      rw [accsSub_length xs2 xs1 (n - 1) (by omega) (by omega)]
      omega

/-- The Taylor sign-factorial `(-1)^k / k!`. -/
def sf (k : ℕ) : ℚ := (-1) ^ k / (k ! : ℚ)

theorem sf_cast (k : ℕ) : ((sf k : ℝ) : ℂ) = (-1) ^ k / (k ! : ℂ) := by
  simp [sf]

/-- `[sf k · centre(x_k), sf (k+1) · centre(x_{k+1}), …]`. -/
def qList (P : ℕ) : ℕ → List Acc → List GQ
  | _, [] => []
  | k, x :: xs => mul (ofQ (sf k)) (accQ P x) :: qList P (k + 1) xs

/-- `Σ_i |sf (k+i)| rad(x_{k+i}) r^i`. -/
def qErr (P : ℕ) (r : ℚ) : ℕ → List Acc → ℚ
  | _, [] => 0
  | k, x :: xs => |sf k| * accRad P x + r * qErr P r (k + 1) xs

theorem qList_close (P : ℕ) (f : ℕ → ℂ) (r : ℚ) (hr : 0 ≤ r) (h : ℂ) (hh : ‖h‖ ≤ (r : ℝ)) :
    ∀ (xs : List Acc) (k : ℕ), AccsOK P f k xs →
      ‖cpeval (cList (fun m => ((sf m : ℝ) : ℂ) * f m) k xs.length) h - peval (qList P k xs) h‖
        ≤ (qErr P r k xs : ℝ)
  | [], k, _ => by simp [cList, cpeval, peval, qErr, qList]
  | x :: xs, k, hx => by
      have ih := qList_close P f r hr h hh xs (k + 1) hx.2
      have hc := accQ_close P (f k) x hx.1
      have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      simp only [List.length_cons, cList, cpeval, qList, peval, qErr, toC_mul, toC_ofQ,
        Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
      have e : ((sf k : ℝ) : ℂ) * f k + h * cpeval (cList (fun m => ((sf m : ℝ) : ℂ) * f m)
            (k + 1) xs.length) h - (((sf k : ℝ) : ℂ) * toC (accQ P x) + h * peval (qList P (k + 1) xs) h)
          = ((sf k : ℝ) : ℂ) * (f k - toC (accQ P x))
            + h * (cpeval (cList (fun m => ((sf m : ℝ) : ℂ) * f m) (k + 1) xs.length) h
              - peval (qList P (k + 1) xs) h) := by ring
      rw [e]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
        (mul_le_mul hh ih (norm_nonneg _) hr')

/-! ## E. The exact expansion of the correction factor. -/

/-- `[a, a w, a w², …]` (`n` terms). -/
def geoList (w : GQ) : GQ → ℕ → List GQ
  | _, 0 => []
  | a, n + 1 => a :: geoList w (mul a w) n

theorem peval_geoList (w : GQ) : ∀ (n : ℕ) (a : GQ) (h : ℂ),
    peval (geoList w a n) h = toC a * ∑ j ∈ Finset.range n, (toC w * h) ^ j
  | 0, a, h => by simp [geoList, peval]
  | n + 1, a, h => by
      simp only [geoList, peval, peval_geoList w n (mul a w) h, toC_mul]
      rw [geom_sum_succ]
      ring

/-- `(c + h)_m` as a polynomial in `h`. -/
def pochList (c : GQ) : ℕ → List GQ
  | 0 => [⟨1, 0⟩]
  | m + 1 => pmul (pochList c m) [add c (ofQ m), ⟨1, 0⟩]

theorem peval_pochList (c : GQ) (h : ℂ) : ∀ m, peval (pochList c m) h = poch (toC c + h) m
  | 0 => by
      have : toC (⟨1, 0⟩ : GQ) = 1 := by apply Complex.ext <;> simp
      simp [pochList, peval, poch, this]
  | m + 1 => by
      have h1 : toC (⟨1, 0⟩ : GQ) = 1 := by apply Complex.ext <;> simp
      simp only [pochList, peval_pmul, peval_pochList c h m, peval, toC_add, toC_ofQ, h1, poch]
      push_cast
      ring

/-- `B_{i+2}/(i+2)!` as a rational (`i ≤ 10`). -/
def beta (i : ℕ) : ℚ := (OrderK.betaN i : ℚ) / (OrderK.Lbeta : ℚ)

theorem beta_cast (i : ℕ) (hi : i ≤ 10) :
    ((beta i : ℝ) : ℂ) = (bernoulli (i + 2) : ℂ) / ((i + 2)! : ℂ) := by
  have hs := OrderK.betaN_spec i hi
  have e : ((beta i : ℚ) : ℝ) = (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) := by
    rw [hs]; simp [beta]
  rw [e]
  push_cast
  rfl

/-- The polynomial part `1/2 + Σ_{i<n} B_{i+2}/(i+2)! (c+h)_{i+1} / N^{i+1}` of the correction. -/
def corrPoly (c : GQ) (N : ℕ) : ℕ → List GQ
  | 0 => [⟨1 / 2, 0⟩]
  | i + 1 => padd (corrPoly c N i) (pscale (ofQ (beta i / (N : ℚ) ^ (i + 1))) (pochList c (i + 1)))

theorem peval_corrPoly (c : GQ) (N : ℕ) (h : ℂ) : ∀ n, n ≤ 11 →
    peval (corrPoly c N n) h = 1 / 2 + ∑ i ∈ Finset.range n,
      (bernoulli (i + 2) : ℂ) * poch (toC c + h) (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)
  | 0, _ => by
      simp only [corrPoly, peval, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      apply Complex.ext <;> simp <;> norm_num
  | i + 1, hi => by
      simp only [corrPoly, peval_padd, peval_pscale, peval_pochList, toC_ofQ,
        peval_corrPoly c N h i (by omega), Finset.sum_range_succ]
      have hb := beta_cast i (by omega)
      have e : (((beta i / (N : ℚ) ^ (i + 1) : ℚ) : ℝ) : ℂ) = ((beta i : ℝ) : ℂ) / (N : ℂ) ^ (i + 1) := by
        push_cast; rfl
      rw [e, hb]
      ring

/-- The correction factor's expansion: geometric part (`J + 1` terms) plus the polynomial part. -/
def gammaList (c : GQ) (N K J : ℕ) : List GQ :=
  padd (geoList (neg (inv (add c (ofQ (-1))))) (mul (ofQ N) (inv (add c (ofQ (-1))))) (J + 1))
    (corrPoly c N (2 * K - 1))

theorem geo_identity (c1 h : ℂ) (N : ℂ) (n : ℕ) (hc1 : c1 ≠ 0) (hch : c1 + h ≠ 0) :
    N / (c1 + h) = N * c1⁻¹ * ∑ j ∈ Finset.range n, (-c1⁻¹ * h) ^ j
      + N * (-h / c1) ^ n / (c1 + h) := by
  set u := -c1⁻¹ * h with hu
  have hu1 : u - 1 ≠ 0 := by
    intro h0
    have : u = 1 := by linear_combination h0
    rw [hu] at this
    apply hch
    field_simp at this
    linear_combination -this
  have hg := geom_sum_mul u n
  have hs : ∑ j ∈ Finset.range n, u ^ j = (u ^ n - 1) / (u - 1) := by
    rw [eq_div_iff hu1]; exact hg
  have hun : (-h / c1) ^ n = u ^ n := by rw [hu]; congr 1; field_simp
  rw [hs, hun]
  have hu1' : u - 1 = -(c1 + h) / c1 := by rw [hu]; field_simp; ring
  rw [hu1']
  field_simp
  ring

theorem emCorr_expand (K N J : ℕ) (hK : 1 ≤ K) (hK6 : K ≤ 6) (c : GQ) (h : ℂ)
    (hnsq : (add c (ofQ (-1))).nsq ≠ 0) (hch : toC c - 1 + h ≠ 0) :
    emCorr K (toC c + h) N = peval (gammaList c N K J) h
      + (N : ℂ) * (-h / (toC c - 1)) ^ (J + 1) / (toC c - 1 + h) := by
  have hc1e : toC (add c (ofQ (-1))) = toC c - 1 := by
    rw [toC_add, toC_ofQ]; push_cast; ring
  have hc1 : toC c - 1 ≠ 0 := by
    intro h0
    have h1 : Complex.normSq (toC (add c (ofQ (-1)))) = 0 := by rw [hc1e, h0, map_zero]
    rw [normSq_toC] at h1
    exact hnsq (by exact_mod_cast h1)
  unfold gammaList
  rw [peval_padd, peval_geoList, peval_corrPoly c N h (2 * K - 1) (by omega)]
  simp only [toC_neg, toC_mul, toC_ofQ, toC_inv _ hnsq, hc1e]
  unfold emCorr
  have hg := geo_identity (toC c - 1) h (N : ℂ) (J + 1) hc1 hch
  have e1 : toC c + h - 1 = toC c - 1 + h := by ring
  rw [e1, hg]
  have e2 : (((N : ℚ) : ℝ) : ℂ) = (N : ℂ) := by push_cast; rfl
  rw [e2]
  have e3 : ∀ i ∈ Finset.range (2 * K - 1),
      (bernoulli (i + 2) : ℂ) * poch (toC c + h) (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)
        = (bernoulli (i + 2) : ℂ) * poch (toC c + h) (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1) :=
    fun _ _ => rfl
  ring

theorem norm_geo_tail_le (c1 h : ℂ) (N : ℕ) (n : ℕ) (R t : ℝ) (hR0 : 0 ≤ R) (hh : ‖h‖ ≤ R)
    (ht : t = c1.im) (hRt : R < t) :
    ‖(N : ℂ) * (-h / c1) ^ n / (c1 + h)‖ ≤ (N : ℝ) * (R / t) ^ n / (t - R) := by
  have ht0 : 0 < t := lt_of_le_of_lt hR0 hRt
  have hc1 : t ≤ ‖c1‖ := by
    rw [ht]; exact le_trans (le_abs_self _) (Complex.abs_im_le_norm c1)
  have hch : t - R ≤ ‖c1 + h‖ := by
    have h1 : |h.im| ≤ ‖h‖ := Complex.abs_im_le_norm h
    have h2 : |(c1 + h).im| ≤ ‖c1 + h‖ := Complex.abs_im_le_norm _
    have h3 : (c1 + h).im = t + h.im := by rw [Complex.add_im, ht]
    rw [h3] at h2
    have := neg_abs_le h.im
    have := le_abs_self (t + h.im)
    linarith
  have hc1pos : 0 < ‖c1‖ := lt_of_lt_of_le ht0 hc1
  rw [norm_div, norm_mul, norm_pow, norm_div, norm_neg, Complex.norm_natCast]
  have hq : ‖h‖ / ‖c1‖ ≤ R / t := by
    rw [div_le_div_iff₀ hc1pos ht0]
    exact mul_le_mul hh hc1 ht0.le hR0
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hTR : 0 < t - R := by linarith
  calc (N : ℝ) * (‖h‖ / ‖c1‖) ^ n / ‖c1 + h‖ ≤ (N : ℝ) * (R / t) ^ n / ‖c1 + h‖ := by
        gcongr
    _ ≤ (N : ℝ) * (R / t) ^ n / (t - R) := by
        apply div_le_div_of_nonneg_left (by positivity) hTR hch

/-! ## F. The Taylor model of the finite part, with the expanded correction factor. -/

/-- `S_k = Σ_{n<N} (log n)^k n^(-c)`. -/
noncomputable def Sk (N : ℕ) (c : ℂ) (k : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 N, ((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c)

/-- `E_k = (log N)^k N^(-c)`. -/
noncomputable def Ek (N : ℕ) (c : ℂ) (k : ℕ) : ℂ := ((Real.log N : ℝ) : ℂ) ^ k * (N : ℂ) ^ (-c)

theorem model_err (K N p : ℕ) (hN : 1 ≤ N) (c h Γ τ : ℂ) (R L GU TU : ℝ) (hc : 0 ≤ c.re)
    (hch : 0 ≤ (c + h).re) (hR : ‖h‖ ≤ R) (hL : Real.log N ≤ L) (hRL : R * L ≤ 1)
    (hexp : emCorr K (c + h) N = Γ + τ) (hΓ : ‖Γ‖ ≤ GU) (hτ : ‖τ‖ ≤ TU) :
    ‖emFinite K (c + h) N
        - (∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Sk N c k)
          + (∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Ek N c k)) * Γ)‖
      ≤ ((N : ℝ) - 1) * ((R * L) ^ (p + 1) * Cp p) + (R * L) ^ (p + 1) * Cp p * GU + TU := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hR
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hterm : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      ‖Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
          - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)‖
        ≤ (R * L) ^ (p + 1) * Cp p := by
    intro n hn1 hnN
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hlognL : Real.log n ≤ L :=
      le_trans (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast hnN)) hL
    have hw : ‖-(h * ((Real.log n : ℝ) : ℂ))‖ ≤ R * L := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogn]
      exact mul_le_mul hR hlognL hlogn hR0
    have hw1 : ‖-(h * ((Real.log n : ℝ) : ℂ))‖ ≤ 1 := le_trans hw hRL
    refine le_trans (exp_taylor_le _ hw1 p) ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw _) (Cp_nonneg p)
  have hpow : ∀ (x : ℝ) (k : ℕ), (-(h * (x : ℂ))) ^ k / (k ! : ℂ)
      = h ^ k * ((-1) ^ k / (k ! : ℂ) * (x : ℂ) ^ k) := by
    intro x k; rw [neg_pow, mul_pow]; ring
  have hS : ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Sk N c k)
      = ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
          * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ) := by
    calc ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Sk N c k)
        = ∑ k ∈ Finset.range (p + 1), ∑ n ∈ Finset.Ico 1 N,
            h ^ k * ((-1) ^ k / (k ! : ℂ) * (((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))) := by
          apply Finset.sum_congr rfl; intro k _; rw [Sk, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ n ∈ Finset.Ico 1 N, ∑ k ∈ Finset.range (p + 1),
            h ^ k * ((-1) ^ k / (k ! : ℂ) * (((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))) :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro n _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _
          rw [hpow]; ring
  have hE : ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Ek N c k)
      = (N : ℂ) ^ (-c) * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log N : ℝ) : ℂ))) ^ k / (k ! : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [hpow, Ek]; ring
  have hfin : emFinite K (c + h) N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
        + (N : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log N : ℝ) : ℂ))) * emCorr K (c + h) N := by
    unfold emFinite
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      exact natCpow_neg_add n (Finset.mem_Ico.mp hn).1 c h
    · rw [natCpow_neg_add N hN c h]
  rw [hS, hE, hfin, hexp]
  set eN := Complex.exp (-(h * ((Real.log N : ℝ) : ℂ))) with heN
  set PN := ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log N : ℝ) : ℂ))) ^ k / (k ! : ℂ) with hPN
  have e : (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
        + (N : ℂ) ^ (-c) * eN * (Γ + τ)
        - ((∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
            * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))
          + (N : ℂ) ^ (-c) * PN * Γ)
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)))
        + ((N : ℂ) ^ (-c) * (eN - PN) * Γ + (N : ℂ) ^ (-c) * eN * τ) := by
    have hsd : (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
          - ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
              * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)
        = ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro n _; ring
    rw [← hsd]
    ring
  rw [e]
  have hNc : ‖(N : ℂ) ^ (-c)‖ ≤ 1 := norm_natCpow_neg_le_one N hN c hc
  have p1 : ‖∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
      ≤ ((N : ℝ) - 1) * ((R * L) ^ (p + 1) * Cp p) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hle : ∀ n ∈ Finset.Ico 1 N, ‖(n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
          ≤ (R * L) ^ (p + 1) * Cp p := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Ico.mp hn
      rw [norm_mul]
      have := hterm n hn1 hnN.le
      have hn' := norm_natCpow_neg_le_one n hn1 c hc
      calc ‖(n : ℂ) ^ (-c)‖ * ‖Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)‖
          ≤ 1 * ((R * L) ^ (p + 1) * Cp p) := by gcongr
        _ = (R * L) ^ (p + 1) * Cp p := one_mul _
    refine le_trans (Finset.sum_le_sum hle) (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    push_cast [Nat.cast_sub hN]
    ring
  have p2 : ‖(N : ℂ) ^ (-c) * (eN - PN) * Γ‖ ≤ (R * L) ^ (p + 1) * Cp p * GU := by
    rw [norm_mul, norm_mul]
    have := hterm N hN le_rfl
    have hT0 : 0 ≤ (R * L) ^ (p + 1) * Cp p :=
      mul_nonneg (pow_nonneg (mul_nonneg hR0 (le_trans hlogN hL)) _) (Cp_nonneg p)
    calc ‖(N : ℂ) ^ (-c)‖ * ‖eN - PN‖ * ‖Γ‖ ≤ 1 * ((R * L) ^ (p + 1) * Cp p) * GU :=
          mul_le_mul (mul_le_mul hNc this (norm_nonneg _) zero_le_one) hΓ (norm_nonneg _)
            (mul_nonneg zero_le_one hT0)
      _ = _ := by ring
  have p3 : ‖(N : ℂ) ^ (-c) * eN * τ‖ ≤ TU := by
    have e3 : (N : ℂ) ^ (-c) * eN = (N : ℂ) ^ (-(c + h)) := by
      rw [heN, natCpow_neg_add N hN c h]
    rw [e3, norm_mul]
    have h1 := norm_natCpow_neg_le_one N hN (c + h) hch
    calc ‖(N : ℂ) ^ (-(c + h))‖ * ‖τ‖ ≤ 1 * TU := by gcongr
      _ = TU := one_mul _
  calc _ ≤ ‖∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
        + (‖(N : ℂ) ^ (-c) * (eN - PN) * Γ‖ + ‖(N : ℂ) ^ (-c) * eN * τ‖) :=
        le_trans (norm_add_le _ _) (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ _ := by linarith

/-! ## G. The EM remainder on `0 ≤ Re s ≤ 1`. -/

theorem em_remainder_region0 (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) (s : ℂ) (hs0 : 0 ≤ s.re)
    (hs1 : s.re ≤ 1) (hsim : 0 < s.im) (B : ℝ) (hsB : s.im ≤ B) (Qr : ℝ) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq 1 B (2 * K + 1) ≤ Qr ^ 2) :
    ‖riemannZeta s - emFinite K s N‖ ≤ CK K * Qr / (N : ℝ) ^ (2 * K) / ((2 * K : ℕ) : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs1' : s ≠ 1 := by
    intro h; rw [h] at hsim; simp at hsim
  have henc := EMOff.em_zeta_orderK_enclosure_odd_ext K hK (s := s)
    (by have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
        push_cast; linarith) hs1' hN
  refine le_trans henc ?_
  have hseq : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im s).symm
  have hmono := pochNormSq_mono s.re s.im 1 B hs0 hs1
    (by rw [abs_of_pos hsim]; exact hsB) (2 * K + 1)
  have hpoch : ‖poch s (2 * K + 1)‖ ≤ Qr := by
    rw [hseq]; exact norm_poch_le s.re s.im (2 * K + 1) Qr hQr0 (le_trans hmono hQ)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤ 1 / (N : ℝ) ^ (2 * K) := by
    have e : (N : ℝ) ^ (-((2 * K : ℕ) : ℝ)) = 1 / (N : ℝ) ^ (2 * K) := by
      rw [Real.rpow_neg hNR.le, Real.rpow_natCast, one_div]
    rw [← e]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    push_cast; linarith
  have hK2 : (0 : ℝ) < ((2 * K : ℕ) : ℝ) := by
    have : 0 < 2 * K := by omega
    exact_mod_cast this
  have hden : ((2 * K : ℕ) : ℝ) ≤ s.re + ((2 * K + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hpn0 : 0 ≤ (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) := by positivity
  have hCK := CK_nonneg K
  change CK K * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
      / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) ≤ _
  calc CK K * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
        / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)
      ≤ CK K * Qr * (1 / (N : ℝ) ^ (2 * K)) / ((2 * K : ℕ) : ℝ) := by
        gcongr
    _ = CK K * Qr / (N : ℝ) ^ (2 * K) / ((2 * K : ℕ) : ℝ) := by ring

/-! ## H. The kernel check. -/

/-- `Cp p` as a rational. -/
def cpQ (p : ℕ) : ℚ := ((p + 2 : ℕ) : ℚ) / (((p + 1)! : ℕ) * ((p + 1 : ℕ) : ℚ))

theorem cpQ_cast (p : ℕ) : ((cpQ p : ℚ) : ℝ) = Cp p := by
  simp [cpQ, Cp]

/-- The model polynomial `M(h)` with exact Gaussian-rational coefficients (accumulator centres). -/
def modelPoly (P : ℕ) (cQ : GQ) (N K J : ℕ) (xs1 xs2 : List Acc) : List GQ :=
  padd (qList P 0 xs1) (pmul (qList P 0 (accsSub xs2 xs1)) (gammaList cQ N K J))

/-- The uniform error budget `G` of `ζ(z) - M(z - c)` on `‖z - c‖ ≤ R`. -/
def budgetQ (P : ℕ) (cQ : GQ) (N K p J : ℕ) (xs1 xs2 : List Acc) (lhi : ℕ) (R ER : ℚ) : ℚ :=
  ER + ((N : ℚ) - 1) * (cpQ p * (R * ((lhi : ℚ) / 2 ^ P)) ^ (p + 1))
    + cpQ p * (R * ((lhi : ℚ) / 2 ^ P)) ^ (p + 1) * pnub R (gammaList cQ N K J)
    + (N : ℚ) * (R / cQ.im) ^ (J + 1) / (cQ.im - R)
    + qErr P R 0 xs1 + qErr P R 0 (accsSub xs2 xs1) * pnub R (gammaList cQ N K J)

/-- The derivative test on `pderiv M = d0 :: Dt`: `(r · ub(Dt) + F)² < |d0|²`. -/
def derivTest (r F : ℚ) : List GQ → Bool
  | [] => false
  | d0 :: Dt => decide (0 ≤ r * pnub r Dt + F) && decide ((r * pnub r Dt + F) ^ 2 < d0.nsq)

/-- **The kernel cell check.** -/
def checkD (P : ℕ) (cQ : GQ) (N K p J : ℕ) (xs1 xs2 : List Acc) (lhi : ℕ) (r ρ F ER : ℚ) : Bool :=
  decide (1 ≤ K) && decide (K ≤ 6) && decide (2 ≤ N) && decide (xs1.length = p + 1) &&
    decide (xs2.length = p + 1) && decide (0 < ρ) && decide (0 ≤ r) &&
    decide (r + ρ ≤ cQ.re) && decide (cQ.re + (r + ρ) ≤ 1) && decide (r + ρ < cQ.im) &&
    decide ((r + ρ) * ((lhi : ℚ) / 2 ^ P) ≤ 1) && decide (0 ≤ F) && decide (0 ≤ ER) &&
    decide (budgetQ P cQ N K p J xs1 xs2 lhi (r + ρ) ER ≤ F * ρ) &&
    derivTest r F (pderiv (modelPoly P cQ N K J xs1 xs2))

theorem derivTest_sound (r F : ℚ) (hr : 0 ≤ r) (D : List GQ) (hD : derivTest r F D = true)
    (h : ℂ) (hh : ‖h‖ ≤ (r : ℝ)) : (F : ℝ) < ‖peval D h‖ := by
  match D, hD with
  | d0 :: Dt, hD =>
    simp only [derivTest, Bool.and_eq_true, decide_eq_true_eq] at hD
    obtain ⟨h0, h1⟩ := hD
    have hlow := norm_peval_cons_ge r hr h hh d0 Dt
    have h0' : (0 : ℝ) ≤ (r : ℝ) * (pnub r Dt : ℝ) + (F : ℝ) := by exact_mod_cast h0
    have h1' : ((r : ℝ) * (pnub r Dt : ℝ) + (F : ℝ)) ^ 2 < (d0.nsq : ℝ) := by exact_mod_cast h1
    rw [← norm_toC_sq] at h1'
    have : (r : ℝ) * (pnub r Dt : ℝ) + (F : ℝ) < ‖toC d0‖ :=
      lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1'
    linarith

/-! ## I. The zero-free cell for `ζ'`. -/

theorem sOfG_eq_toC (σ t : ℝ) (cQ : GQ) (hσ : σ = (cQ.re : ℝ)) (ht : t = (cQ.im : ℝ)) :
    sOfG σ t = toC cQ := by
  apply Complex.ext <;> simp [sOfG, hσ, ht]

set_option maxHeartbeats 4000000 in
/-- **A zero-free cell of `ζ'`.**  The evaluator invariants after `N - 1` and `N` terms at the centre
    `c = σ + i t`, the kernel check `checkD … = true`, the order-(2K+1) remainder certificate `hQ`
    and the remainder budget `hER` give `ζ'(s) ≠ 0` for every `s` with `‖s - c‖ ≤ r`. -/
theorem cell_deriv_ne_zero (cf : Cfg) (σ t : ℝ) (cQ : GQ) (hσ : σ = (cQ.re : ℝ))
    (ht : t = (cQ.im : ℝ)) (K N p J : ℕ) (s1 s2 : StO) (h1 : InvO cf σ t (N - 1) s1)
    (h2 : InvO cf σ t N s2) (r ρ F ER : ℚ)
    (hchk : checkD cf.P cQ N K p J s1.acc s2.acc s2.lhi r ρ F ER = true)
    (Qr : ℝ) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq 1 ((cQ.im : ℝ) + ((r : ℝ) + (ρ : ℝ))) (2 * K + 1) ≤ Qr ^ 2)
    (hER : CK K * Qr / (N : ℝ) ^ (2 * K) / ((2 * K : ℕ) : ℝ) ≤ (ER : ℝ)) :
    ∀ s : ℂ, ‖s - sOfG σ t‖ ≤ (r : ℝ) → deriv riemannZeta s ≠ 0 := by
  simp only [checkD, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, hl1⟩, hl2⟩, hρ⟩, hr⟩, hRre⟩, hRre1⟩, hRim⟩, hRL⟩, hF0⟩,
    hER0⟩, hbud⟩, hder⟩ := hchk
  set R : ℚ := r + ρ with hRdef
  set c : ℂ := sOfG σ t with hcdef
  have hcC : c = toC cQ := sOfG_eq_toC σ t cQ hσ ht
  have hcre : c.re = (cQ.re : ℝ) := by rw [hcC, toC_re]
  have hcim : c.im = (cQ.im : ℝ) := by rw [hcC, toC_im]
  have hRR : (R : ℝ) = (r : ℝ) + (ρ : ℝ) := by rw [hRdef]; push_cast; ring
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hrR : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hR0 : (0 : ℚ) ≤ R := by rw [hRdef]; linarith
  have hR0R : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR0
  have hRreR : (R : ℝ) ≤ (cQ.re : ℝ) := by exact_mod_cast hRre
  have hRre1R : (cQ.re : ℝ) + (R : ℝ) ≤ 1 := by exact_mod_cast hRre1
  have hRimR : (R : ℝ) < (cQ.im : ℝ) := by exact_mod_cast hRim
  have hN1 : 1 ≤ N := by omega
  -- the log bracket
  set Lq : ℚ := (s2.lhi : ℚ) / 2 ^ cf.P with hLq
  have hP : (0 : ℝ) < 2 ^ cf.P := by positivity
  have hlogN : Real.log N ≤ (Lq : ℝ) := by
    have hb := h2.2.2.2.1
    have e : (Lq : ℝ) = (s2.lhi : ℝ) / 2 ^ cf.P := by rw [hLq]; push_cast; ring
    rw [e, le_div_iff₀ hP]
    exact hb
  have hRLR : (R : ℝ) * (Lq : ℝ) ≤ 1 := by exact_mod_cast hRL
  -- the gamma list and its bound
  set gam := gammaList cQ N K J with hgam
  have hnsq : (add cQ (ofQ (-1))).nsq ≠ 0 := by
    intro h0
    have hpos : (0 : ℚ) < (add cQ (ofQ (-1))).nsq := by
      simp only [nsq, add, ofQ]
      have : (0 : ℚ) < cQ.im := lt_of_le_of_lt hR0 hRim
      nlinarith [sq_nonneg (cQ.re + -1)]
    linarith
  -- STEP 1: the uniform bound on ‖ζ z - M(z - c)‖ on the closed disc of radius R
  have hunif : ∀ z : ℂ, ‖z - c‖ ≤ (R : ℝ) →
      ‖riemannZeta z - peval (modelPoly cf.P cQ N K J s1.acc s2.acc) (z - c)‖
        ≤ (budgetQ cf.P cQ N K p J s1.acc s2.acc s2.lhi R ER : ℝ) := by
    intro z hz
    set h := z - c with hh
    have hzc : z = c + h := by rw [hh]; ring
    have hhre : |h.re| ≤ (R : ℝ) := le_trans (Complex.abs_re_le_norm h) hz
    have hhim : |h.im| ≤ (R : ℝ) := le_trans (Complex.abs_im_le_norm h) hz
    rw [abs_le] at hhre hhim
    have hzre : z.re = c.re + h.re := by rw [hzc, Complex.add_re]
    have hzim : z.im = c.im + h.im := by rw [hzc, Complex.add_im]
    -- remainder
    have hrem := em_remainder_region0 K N hK1 hN1 z (by rw [hzre, hcre]; linarith)
      (by rw [hzre, hcre]; linarith) (by rw [hzim, hcim]; linarith)
      ((cQ.im : ℝ) + ((r : ℝ) + (ρ : ℝ))) (by rw [hzim, hcim, ← hRR]; linarith) Qr hQr0 hQ
    -- the correction expansion
    have hch1 : toC cQ - 1 + h ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.sub_im, toC_im, Complex.one_im, sub_zero,
        Complex.zero_im] at this
      linarith
    have hexp0 := emCorr_expand K N J hK1 hK6 cQ h hnsq hch1
    have hexp : emCorr K (c + h) N = peval gam h
        + (N : ℂ) * (-h / (toC cQ - 1)) ^ (J + 1) / (toC cQ - 1 + h) := by
      rw [hcC]; exact hexp0
    have hΓ := norm_peval_le R hR0 h hz gam
    have hτ := norm_geo_tail_le (toC cQ - 1) h N (J + 1) (R : ℝ) (cQ.im : ℝ) hR0R hz
      (by simp) hRimR
    have hmod := model_err K N p hN1 c h (peval gam h)
      ((N : ℂ) * (-h / (toC cQ - 1)) ^ (J + 1) / (toC cQ - 1 + h)) (R : ℝ) (Lq : ℝ)
      (pnub R gam : ℝ) ((N : ℝ) * ((R : ℝ) / (cQ.im : ℝ)) ^ (J + 1) / ((cQ.im : ℝ) - (R : ℝ)))
      (by rw [hcre]; linarith) (by rw [← hzc, hzre, hcre]; linarith) hz hlogN hRLR hexp hΓ hτ
    rw [← hzc] at hmod
    -- the accumulator centres
    have hS1 : AccsOK cf.P (fun k => Sk N c k) 0 s1.acc := by
      have := h1.2.2.2.2
      have e : (fun k => psumK σ t k (N - 1)) = (fun k => Sk N c k) := by
        funext k; simp only [psumK, Sk, hcdef]; rw [show N - 1 + 1 = N by omega]
      rwa [e] at this
    have hE1 : AccsOK cf.P (fun k => Ek N c k) 0 (accsSub s2.acc s1.acc) := by
      have := accsSub_ok cf.P (fun k => psumK σ t k N) (fun k => psumK σ t k (N - 1)) s2.acc s1.acc 0
        h2.2.2.2.2 h1.2.2.2.2
      have e : (fun j => psumK σ t j N - psumK σ t j (N - 1)) = (fun k => Ek N c k) := by
        funext k
        have hs := psumK_succ σ t k (N - 1)
        rw [show N - 1 + 1 = N by omega] at hs
        rw [hs, Ek, hcdef]; ring
      rwa [e] at this
    have hlenE : (accsSub s2.acc s1.acc).length = p + 1 := accsSub_length _ _ _ hl2 hl1
    have hq1 := qList_close cf.P (fun k => Sk N c k) R hR0 h hz s1.acc 0 hS1
    have hq2 := qList_close cf.P (fun k => Ek N c k) R hR0 h hz (accsSub s2.acc s1.acc) 0 hE1
    rw [hl1] at hq1
    rw [hlenE] at hq2
    have hcpS : cpeval (cList (fun m => ((sf m : ℝ) : ℂ) * Sk N c m) 0 (p + 1)) h
        = ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Sk N c k) := by
      rw [cpeval_cList]; apply Finset.sum_congr rfl; intro k _; rw [zero_add, sf_cast]; ring
    have hcpE : cpeval (cList (fun m => ((sf m : ℝ) : ℂ) * Ek N c m) 0 (p + 1)) h
        = ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Ek N c k) := by
      rw [cpeval_cList]; apply Finset.sum_congr rfl; intro k _; rw [zero_add, sf_cast]; ring
    rw [hcpS] at hq1
    rw [hcpE] at hq2
    have hM : peval (modelPoly cf.P cQ N K J s1.acc s2.acc) h
        = peval (qList cf.P 0 s1.acc) h + peval (qList cf.P 0 (accsSub s2.acc s1.acc)) h * peval gam h := by
      simp only [modelPoly, peval_padd, peval_pmul, hgam]
    rw [hM]
    set A := ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Sk N c k)
    set B := ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Ek N c k)
    have hsplit : riemannZeta z - (peval (qList cf.P 0 s1.acc) h
          + peval (qList cf.P 0 (accsSub s2.acc s1.acc)) h * peval gam h)
        = (riemannZeta z - emFinite K z N) + (emFinite K z N - (A + B * peval gam h))
          + (A - peval (qList cf.P 0 s1.acc) h)
          + (B - peval (qList cf.P 0 (accsSub s2.acc s1.acc)) h) * peval gam h := by ring
    rw [hsplit]
    have hprod : ‖(B - peval (qList cf.P 0 (accsSub s2.acc s1.acc)) h) * peval gam h‖
        ≤ (qErr cf.P R 0 (accsSub s2.acc s1.acc) : ℝ) * (pnub R gam : ℝ) := by
      rw [norm_mul]; exact mul_le_mul hq2 hΓ (norm_nonneg _) (le_trans (norm_nonneg _) hq2)
    refine le_trans norm_add₄_le ?_
    have hbudget : (budgetQ cf.P cQ N K p J s1.acc s2.acc s2.lhi R ER : ℝ)
        = (ER : ℝ) + ((N : ℝ) - 1) * (((R : ℝ) * (Lq : ℝ)) ^ (p + 1) * Cp p)
          + ((R : ℝ) * (Lq : ℝ)) ^ (p + 1) * Cp p * (pnub R gam : ℝ)
          + (N : ℝ) * ((R : ℝ) / (cQ.im : ℝ)) ^ (J + 1) / ((cQ.im : ℝ) - (R : ℝ))
          + (qErr cf.P R 0 s1.acc : ℝ)
          + (qErr cf.P R 0 (accsSub s2.acc s1.acc) : ℝ) * (pnub R gam : ℝ) := by
      simp only [budgetQ, hLq, hgam]
      push_cast
      rw [← cpQ_cast]
      ring
    rw [hbudget]
    linarith
  -- STEP 2: Cauchy's estimate at each point of the inner disc
  intro s hs
  set g : ℂ → ℂ := fun z => peval (modelPoly cf.P cQ N K J s1.acc s2.acc) (z - c) with hgdef
  set f : ℂ → ℂ := fun z => riemannZeta z - g z with hfdef
  have hdiffz : ∀ z : ℂ, ‖z - c‖ ≤ (R : ℝ) → DifferentiableAt ℂ riemannZeta z := by
    intro z hz
    apply differentiableAt_riemannZeta
    intro h0
    have him : |(z - c).im| ≤ (R : ℝ) := le_trans (Complex.abs_im_le_norm _) hz
    rw [h0, Complex.sub_im, Complex.one_im, hcim, abs_le] at him
    linarith [him.1]
  have hg' : ∀ z : ℂ, HasDerivAt g (peval (pderiv (modelPoly cf.P cQ N K J s1.acc s2.acc)) (z - c)) z :=
    fun z => (hasDerivAt_peval _ (z - c)).comp_sub_const z c
  have hsub : ∀ z ∈ Metric.closedBall s (ρ : ℝ), ‖z - c‖ ≤ (R : ℝ) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    calc ‖z - c‖ = ‖(z - s) + (s - c)‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s - c‖ := norm_add_le _ _
      _ ≤ (ρ : ℝ) + (r : ℝ) := add_le_add hz hs
      _ = (R : ℝ) := by rw [hRR]; ring
  have hdiffOn : DifferentiableOn ℂ f (Metric.closedBall s (ρ : ℝ)) := by
    intro z hz
    exact ((hdiffz z (hsub z hz)).sub (hg' z).differentiableAt).differentiableWithinAt
  have hcont : DiffContOnCl ℂ f (Metric.ball s (ρ : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s (ne_of_gt hρR)]
    exact hdiffOn
  have hsph : ∀ z ∈ Metric.sphere s (ρ : ℝ), ‖f z‖ ≤ (budgetQ cf.P cQ N K p J s1.acc s2.acc s2.lhi R ER : ℝ) := by
    intro z hz
    exact hunif z (hsub z (Metric.sphere_subset_closedBall hz))
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρR hcont hsph
  have hbudR : (budgetQ cf.P cQ N K p J s1.acc s2.acc s2.lhi R ER : ℝ) ≤ (F : ℝ) * (ρ : ℝ) := by
    exact_mod_cast hbud
  have hfF : ‖deriv f s‖ ≤ (F : ℝ) := by
    refine le_trans hcauchy ?_
    rw [div_le_iff₀ hρR]; exact hbudR
  -- STEP 3: ζ'(s) = f'(s) + M'(s - c), and ‖M'(s - c)‖ > F
  have hzs : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (hdiffz s (by linarith [hsub s (Metric.mem_closedBall_self hρR.le)])).hasDerivAt
  have hfs : HasDerivAt f (deriv riemannZeta s - peval (pderiv (modelPoly cf.P cQ N K J s1.acc s2.acc)) (s - c)) s :=
    hzs.sub (hg' s)
  rw [hfs.deriv] at hfF
  have hlow := derivTest_sound r F hr _ hder (s - c) hs
  intro h0
  rw [h0, zero_sub, norm_neg] at hfF
  linarith

end ArbEcon.Off.SpD
