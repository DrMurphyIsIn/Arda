"""BUILDER emitter: assemble telperion/examples/li_positivity/lean/Crux/Crux2_kappa_certify.lean from
(i) hand-written Lean sections (generic lemmas, path graph, Schur test, continuous Lemma A, Schur link) and
(ii) four Schur-complement certificate cores (JSON from schur_core.py / schur_core_file_fixed.py).
Usage (research-dir layout): python3 builder/emit_crux2.py OUT.lean [TAMPER]   (TAMPER = 'pivot' | 'entry' | 'delta' produces a negative-control twin)
conjecture1_proved = False."""
import json, sys, os

B = os.path.dirname(os.path.abspath(__file__))
K = os.path.dirname(B)

CORES = [
    ('Core_x6996_even', os.path.join(K, 'idea_certs', 'schur_core_k8.json'),
     'x = e^{249/128} = 6.9958 (a = 249/256; prime powers 2, 3, 4, 5), EVEN sector.  M = leading 450 x 450 '
     'Legendre block of Zhu-type reduction R_{T#} (T# = 560, beta* = 0.1068), lam0 = 4.39e-28.  Arb: '
     'C - lam0 I >= 1e-40 I (verified LDL^T, residual 2.9e-72), Schur complement radius 4.3e-72.'),
    ('Core_x6996_odd', os.path.join(K, 'idea_certs', 'schur_core_k8_odd.json'),
     'x = 6.9958, ODD sector.  M = leading 620 x 620 Legendre block of R_{T#} (T# = 800, beta* = 0.464), '
     'lam0 = 1.25e-24.  Arb: C - lam0 I >= 1e-40 I (residual 5.8e-72), Schur radius 1.5e-72.'),
    ('Core_x11006_even', os.path.join(B, 'outputs', 'schur_core_x11_even_fixed.json'),
     'x = e^{307/128} = 11.006 (a = 307/256; prime powers 2, 3, 4, 5, 7, 8, 9, 11), EVEN sector.  M = leading '
     '2300 x 2300 Legendre block of the window-aware reduction R\'\' (eps = 0.34, w = 66, Tc = 1170, Tk = 1698, '
     'Tmax = 2457), lam0 = 6.6018e-49.  Arb (matrix reloaded from the saved 70-digit file with radii inflated '
     'by 2% + 1e-69 relative): C - lam0 I >= 1e-55 I (verified Cholesky), Schur complement box.'),
    ('Core_x11006_odd', os.path.join(B, 'outputs', 'schur_core_x11_odd_fixed.json'),
     'x = 11.006, ODD sector.  M = leading 2300 x 2300 Legendre block of R\'\' (Tc = 2000, Tk = 2528, '
     'Tmax = 3287), lam0 = 4.4579e-45.  Arb: C - lam0 I >= 1e-55 I (verified Cholesky), Schur complement box.'),
]


def q(pq):
    p, qq = pq
    return "(%d : ℚ)" % p if qq == 1 else "((%d : ℚ) / %d)" % (p, qq)


def r(pq):
    p, qq = pq
    return "(%d : ℝ)" % p if qq == 1 else "((%d : ℝ) / %d)" % (p, qq)


def core_section(ns, fn, desc, tamper=None):
    d = json.load(open(fn))
    k = d['k']
    S = [[list(x) for x in row] for row in d['S']]
    L, D = d['L'], [list(x) for x in d['D']]
    delta = list(d['delta'])
    if tamper == 'pivot':                      # change one pivot numerator by 1 (1 part in 10^300)
        D[3][0] += 1
    elif tamper == 'entry':                    # move one Schur entry by one unit in the last digit
        S[2][5][0] += 7
        S[5][2][0] += 7
    elif tamper == 'delta':                    # triple delta
        delta[0] *= 3
    rows = ["![" + ", ".join(q(S[i][j]) for j in range(k)) + "]" for i in range(k)]
    Sq = "![" + ",\n    ".join(rows) + "]"
    terms = []
    for m in range(k):
        lin = " + ".join("%s * v %d" % (r(L[i][m]), i) for i in range(m, k) if L[i][m][0] != 0)
        terms.append("%s * (%s) ^ 2" % (r(D[m]), lin))
    rhs = "\n    + ".join(terms)
    return f'''
namespace {ns}

/-!
### Certificate core `{ns}`
{desc}
The kernel checks only the exact rational part below; the Arb facts are the hypotheses `hbox`, `hC` of
`core_posdef` / `core_schur`.
-/

/-- Arb-computed Schur complement, rounded to rationals with denominator `10^{d['P']}`. -/
def Sq : Fin {k} → Fin {k} → ℚ :=
  {Sq}

/-- `Sq` as a real matrix. -/
noncomputable def Smat : Fin {k} → Fin {k} → ℝ := fun i j => (Sq i j : ℝ)

/-- entrywise half-width covering the Arb ball radius of the Schur complement and the rounding. -/
noncomputable def w0 : ℝ := {r(d['w0'])}

/-- exact lower bound for the form of `Smat`. -/
noncomputable def δ : ℝ := {r(delta)}

/-- EXACT rational congruence `Sq - δ I = L D Lᵀ`, written as a sum of squares (closed by `ring`). -/
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

theorem box_margin : ({k} : ℝ) * w0 < δ := by norm_num [w0, δ]

/-- Every real `{k} x {k}` matrix in the Arb box around `Smat` is positive definite. -/
theorem core_posdef (G : Fin {k} → Fin {k} → ℝ) (hbox : ∀ i j, |G i j - Smat i j| ≤ w0)
    (v : Fin {k} → ℝ) (hv : v ≠ 0) : 0 < qf G v :=
  posdef_of_box G Smat w0 δ hbox Smat_ge box_margin v hv

/-- For every real symmetric block matrix `[[A, B], [Bᵀ, C]]` (`C` of any finite size) with `C` positive
definite and Schur complement in the Arb box, the block matrix is positive semidefinite.  With the block
matrix `= M - lam0 I` this is `lam_min(M) >= lam0`. -/
theorem core_schur {{m : Type*}} [Fintype m] [DecidableEq m]
    (A : Matrix (Fin {k}) (Fin {k}) ℝ) (hA : A.IsHermitian) (B : Matrix (Fin {k}) m ℝ)
    (C : Matrix m m ℝ) (hC : C.PosDef) (hbox : ∀ i j, |(A - B * C⁻¹ * Bᴴ) i j - Smat i j| ≤ w0) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef :=
  schur_link Smat w0 δ Smat_ge box_margin A hA B C hC hbox

end {ns}
'''


def main():
    out = sys.argv[1]
    tamper = sys.argv[2] if len(sys.argv) > 2 else None
    header = open(os.path.join(B, 'lean_parts', 'header.lean.part')).read()
    path = open(os.path.join(B, 'lean_parts', 'pre_path.lean.part')).read()
    stest = open(os.path.join(B, 'lean_parts', 'pre_schurtest.lean.part')).read()
    lemA = open(os.path.join(B, 'lean_parts', 'pre_lemmaA.lean.part')).read()
    slink = open(os.path.join(B, 'lean_parts', 'pre_schurlink.lean.part')).read()
    extra = open(os.path.join(B, 'lean_parts', 'extra.lean.part')).read()
    parts = [header,
             '\nimport Mathlib\n\nopen Finset Matrix MeasureTheory Real\n\nnamespace Crux2KappaCertify\n',
             '\n/-! ## 1. Generic finite-dimensional lemmas (box lemma, Schur-complement link, assembly) -/\n',
             slink, extra,
             '\n/-! ## 2. Discrete cores of Lemma A (path graph) and Lemma A\' (weighted Schur test) -/\n',
             '\nnamespace PathGraph\n', path, '\nend PathGraph\n',
             '\nnamespace SchurTest\n', stest, '\nend SchurTest\n',
             '\n/-! ## 3. Lemma A in continuous form (window-aware comb bound) -/\n',
             '\nnamespace LemmaA\n', lemA, '\nend LemmaA\n',
             '\n/-! ## 4. Certificate cores -/\n']
    names = []
    for i, (ns, fn, desc) in enumerate(CORES):
        tm = tamper if (tamper and i == 3) else None      # tamper the x = 11.006 odd core only
        parts.append(core_section(ns, fn, desc, tm))
        names.append(ns)
    parts.append('\nend Crux2KappaCertify\n\n')
    prints = ['block_assembly', 'schur_link', 'posdef_of_box', 'PathGraph.path_quad_le', 'SchurTest.schur_test',
              'LemmaA.W_rec', 'LemmaA.shift_bound', 'LemmaA.shift_bound_signed', 'LemmaA.comb_bound',
              'LemmaA.prime_comb_bound']
    for ns in names:
        prints += [ns + '.Sq_ldl', ns + '.core_posdef', ns + '.core_schur']
    parts.append('\n'.join('#print axioms Crux2KappaCertify.%s' % p for p in prints) + '\n')
    s = ''.join(parts)
    open(out, 'w').write(s)
    print('wrote', out, len(s), 'chars')


if __name__ == '__main__':
    main()
