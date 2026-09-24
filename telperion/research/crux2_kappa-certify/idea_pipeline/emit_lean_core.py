"""Emit the Lean kernel check for the Schur-complement core of the a = 249/256 even-sector certificate."""
import json, sys
d = json.load(open(sys.argv[1]))
sector = sys.argv[3] if len(sys.argv) > 3 else 'even'
ns = sys.argv[4] if len(sys.argv) > 4 else ('KappaWindowCore' if sector == 'even' else 'KappaWindowCoreOdd')
window_desc = sys.argv[5] if len(sys.argv) > 5 else None
k = d['k']
def q(pq):
    p, qq = pq
    if qq == 1:
        return "(%d : ℚ)" % p
    return "((%d : ℚ) / %d)" % (p, qq)
def r(pq):
    p, qq = pq
    if qq == 1:
        return "(%d : ℝ)" % p
    return "((%d : ℝ) / %d)" % (p, qq)
S = d['S']; L = d['L']; D = d['D']
rows = []
for i in range(k):
    rows.append("![" + ", ".join(q(S[i][j]) for j in range(k)) + "]")
Sq = "![" + ",\n    ".join(rows) + "]"
# RHS of the identity: sum_m D_m (sum_i L_im v_i)^2   (L lower unit triangular: L[i][m], i >= m)
terms = []
for m in range(k):
    lin = " + ".join("%s * v %d" % (r(L[i][m]), i) for i in range(m, k) if L[i][m][0] != 0)
    terms.append("%s * (%s) ^ 2" % (r(D[m]), lin))
rhs = "\n    + ".join(terms)
w0 = r(d['w0']); delta = r(d['delta'])
lean = f'''import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Kernel-checked core of the window-Weil-form certificate at a = 249/256 ({sector} sector)

`conjecture1_proved = False`.  Nothing here is about RH beyond one finite window.

**What the kernel checks.**  `core_posdef`: every real `{k} x {k}` matrix `G` whose entries lie within
`w0` of the explicit rational matrix `Sq` is positive definite; the load-bearing step is the EXACT
rational congruence `Sq - delta I = L D L^T` (`Sq_ldl`, closed by `ring`), plus a Cauchy-Schwarz box
lemma (`posdef_of_box`, generic).

**What it means (trust boundary, NOT kernel-checked).**  `Sq` is the Arb-computed Schur complement
`S = (A - lam0 I) - B (C - lam0 I)^{{-1}} B^T`, `lam0 = {d['lam0']}`, of the leading 450 x 450 Legendre block
`M = [[A, B], [B^T, C]]` of Zhu's reduced form `R_{{T#}}` (T# = 560 even / 800 odd) of the window Weil form on `L^2[-a, a]`,
`a = 249/256` (`x = e^{{2a}} = 6.9958`, prime powers 2, 3, 4, 5), {sector} sector, with `A` the first {k} modes.
Arb (python-flint 0.6.0, 256 bits) certifies: `|S_ij - Sq_ij| <= w0` for all entries, and
`C - lam0 I > 0` (verified LDL^T, residual {d['C_certified_resid'].replace('+/-', 'pm')}).  Then `S > 0` gives
`M - lam0 I > 0`; with the quadrature, tail and envelope bounds of `certify.py` this yields
{'`Q(f) >= 4.39e-28 ||f||^2` on the even sector (the odd sector is certified separately, >= 1.26e-24).' if sector == 'even' else '`Q(f) >= 1.26e-24 ||f||^2` on the odd sector (the even sector is certified separately, >= 4.39e-28).'}
-/

open Finset

namespace {ns}

/-- The quadratic form of a (function-)matrix. -/
def qf {{n : ℕ}} (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ := ∑ i, ∑ j, v i * G i j * v j

lemma qf_sub {{n : ℕ}} (G S : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qf G v - qf S v = qf (fun i j => G i j - S i j) v := by
  unfold qf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma abs_qf_le {{n : ℕ}} (E : Fin n → Fin n → ℝ) (w : ℝ) (h : ∀ i j, |E i j| ≤ w)
    (v : Fin n → ℝ) : |qf E v| ≤ w * (∑ i, |v i|) ^ 2 := by
  unfold qf
  calc |∑ i, ∑ j, v i * E i j * v j|
      ≤ ∑ i, |∑ j, v i * E i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |v i * E i j * v j| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, w * (|v i| * |v j|) := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        rw [abs_mul, abs_mul]
        have h1 := h i j
        have h2 : 0 ≤ |v i| * |v j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        calc |v i| * |E i j| * |v j| = |E i j| * (|v i| * |v j|) := by ring
          _ ≤ w * (|v i| * |v j|) := mul_le_mul_of_nonneg_right h1 h2
    _ = w * (∑ i, |v i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]

lemma sum_abs_sq_le {{n : ℕ}} (v : Fin n → ℝ) : (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * ∑ i, v i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |v i|)
  simpa [sq_abs] using h

/-- Generic box lemma: a matrix within `w` (entrywise) of a matrix whose form is `>= delta |v|^2`,
with `n w < delta`, is positive definite. -/
theorem posdef_of_box {{n : ℕ}} (G S : Fin n → Fin n → ℝ) (w δ : ℝ)
    (hbox : ∀ i j, |G i j - S i j| ≤ w) (hS : ∀ v : Fin n → ℝ, δ * ∑ i, v i ^ 2 ≤ qf S v)
    (hδ : (n : ℝ) * w < δ) (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < qf G v := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv
  have hw : 0 ≤ w := le_trans (abs_nonneg _) (hbox i0 i0)
  have hpos : 0 < ∑ i, v i ^ 2 :=
    lt_of_lt_of_le (by simpa using pow_pos (abs_pos.mpr hi0) 2)
      (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i0))
  have h1 := abs_qf_le (fun i j => G i j - S i j) w hbox v
  have h2 := sum_abs_sq_le v
  have h3 := hS v
  have hsub := qf_sub G S v
  have h4 : -(w * (∑ i, |v i|) ^ 2) ≤ qf (fun i j => G i j - S i j) v := by
    have := neg_abs_le (qf (fun i j => G i j - S i j) v)
    linarith
  have h5 : w * (∑ i, |v i|) ^ 2 ≤ w * ((n : ℝ) * ∑ i, v i ^ 2) := mul_le_mul_of_nonneg_left h2 hw
  nlinarith

/-- Arb-computed Schur complement (rounded to rationals with denominator 10^{d['P']}). -/
def Sq : Fin {k} → Fin {k} → ℚ :=
  {Sq}

noncomputable def Smat : Fin {k} → Fin {k} → ℝ := fun i j => (Sq i j : ℝ)

/-- entrywise half-width covering the Arb ball radius and the rounding. -/
noncomputable def w0 : ℝ := {w0}

/-- the certified lower bound for the form of `Smat` -/
noncomputable def δ : ℝ := {delta}

/-- EXACT rational congruence `Sq - delta I = L D L^T`, written as a sum of squares. -/
theorem Sq_ldl (v : Fin {k} → ℝ) :
    qf Smat v - δ * ∑ i, v i ^ 2 =
    {rhs} := by
  simp only [qf, Smat, Sq, δ, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  push_cast
  ring

theorem Smat_ge (v : Fin {k} → ℝ) : δ * ∑ i, v i ^ 2 ≤ qf Smat v := by
  have h := Sq_ldl v
  have hp : 0 ≤
    {rhs} := by positivity
  linarith

/-- **Kernel-checked core.**  Every matrix in the Arb box around the Schur complement is positive definite. -/
theorem core_posdef (G : Fin {k} → Fin {k} → ℝ) (hbox : ∀ i j, |G i j - Smat i j| ≤ w0)
    (v : Fin {k} → ℝ) (hv : v ≠ 0) : 0 < qf G v :=
  posdef_of_box G Smat w0 δ hbox Smat_ge (by norm_num [w0, δ]) v hv

end {ns}

#print axioms {ns}.core_posdef
'''
if window_desc:
    lean = lean.replace("`a = 249/256` (`x = e^{2a} = 6.9958`, prime powers 2, 3, 4, 5)", window_desc)
    lean = lean.replace("of Zhu's reduced form `R_{T#}` (T# = 560 even / 800 odd) of the window Weil form",
                        "of the window-aware reduced form `R''` (Lemmas A, B) of the window Weil form")
    lean = lean.replace("{'`Q(f) >= 4.39e-28 ||f||^2` on the even sector (the odd sector is certified separately, >= 1.26e-24).' if sector == 'even' else '`Q(f) >= 1.26e-24 ||f||^2` on the odd sector (the even sector is certified separately, >= 4.39e-28).'}",
                        "the certified sector bound of the x = 11.006 certificate (see certify_wa.py / NOTES.md).")
open(sys.argv[2], 'w').write(lean)
print("wrote", sys.argv[2], len(lean), "chars")
