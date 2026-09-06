"""Probe: the P-vs-NP SoS pseudo-expectation obligation `0 <= pe(s^2)` certifies via
the SAME exact-rational PSD/SOS engine RH's Weil/Jensen minors and BG's SOS base use.

Validates the monitor's shape-match (Hsq.lean:hsq_of_subsetForm) with a concrete
instance, parallel to the BG Handelman probe.  `0 <= pe(s^2)` for all degree-<=d s
<=> the degree-2d moment matrix M[u,v] = pe(x_u x_v) is PSD.  We build M for a small
satisfiable 3-XOR pseudo-expectation and certify PSD by an EXACT rational LDL^T (all
pivots >= 0) -- an SOS/PSD Gram certificate, the emit_sos / WorstCorner shape.
Offline, exact rationals.
"""
import itertools
from fractions import Fraction as F
import sympy as sp

# ---- a small satisfiable 3-XOR: x1 x2 x3 = 1, xi in {+-1}.  A 2-point mixture of
# solutions (not the fully-symmetric measure, which collapses to the identity) gives a
# STRUCTURED rank-deficient PSD moment matrix -- a genuine SoS-boundary object. ----
sols = [(1, 1, 1), (1, -1, -1)]           # both satisfy x1 x2 x3 = 1
w = [F(1, 2), F(1, 2)]                      # mixture weights (pe = sum_k w_k eval_{sols[k]})
def pe(monomial_idx):
    """pseudo-expectation of prod_{i in idx} x_i under the mixture measure (exact)."""
    tot = F(0)
    for wk, s in zip(w, sols):
        p = 1
        for i in monomial_idx:
            p *= s[i]
        tot += wk * p
    return tot

# degree-1 monomial basis: 1, x1, x2, x3  (indices: () , (0,), (1,), (2,))
basis = [(), (0,), (1,), (2,)]
def mono_mul(a, b):
    # x_i^2 = 1 (spins): symmetric difference of index multisets
    from collections import Counter
    c = Counter(a) + Counter(b)
    return tuple(sorted(i for i, k in c.items() if k % 2))

# moment matrix M[u,v] = pe(basis_u * basis_v), exact rational
n = len(basis)
M = [[pe(mono_mul(basis[i], basis[j])) for j in range(n)] for i in range(n)]
print("moment matrix M (pe(x_u x_v), exact):")
for row in M:
    print("  ", [str(x) for x in row])

# ---- EXACT rational LDL^T: PSD iff all pivots >= 0 (the PSD/SOS certificate) ----
import copy
A = copy.deepcopy(M)
L = [[F(0)]*n for _ in range(n)]
D = [F(0)]*n
psd = True
for j in range(n):
    d = A[j][j] - sum(L[j][k]**2 * D[k] for k in range(j))
    D[j] = d
    L[j][j] = F(1)
    if d < 0:
        psd = False
    for i in range(j+1, n):
        if d == 0:
            L[i][j] = F(0)
        else:
            L[i][j] = (A[i][j] - sum(L[i][k]*L[j][k]*D[k] for k in range(j))) / d
print(f"\nexact LDL^T pivots D = {[str(x) for x in D]}")
print(f"all pivots >= 0  ->  moment matrix PSD:  {psd and all(x >= 0 for x in D)}")

# ---- 0 <= pe(s^2) for a sample s = x1 - x2  (=> c^T M c with c over basis) ----
c = {(0,): F(1), (1,): F(-1)}
# pe((x1 - x2)^2) = pe(x1^2) - 2 pe(x1 x2) + pe(x2^2)
val = pe((0,0)) - 2*pe((0,1)) + pe((1,1))
cvec = [c.get(b, F(0)) for b in basis]
quad = sum(cvec[i]*cvec[j]*M[i][j] for i in range(n) for j in range(n))
print(f"\npe((x1 - x2)^2) = {val}   (direct)   == c^T M c = {quad}   (moment form): {val == quad}")
print(f"0 <= pe((x1 - x2)^2): {val >= 0}")

# ---- SOS reading: M = sum_k D_k (L col_k)(L col_k)^T is an SOS/PSD Gram (emit_sos shape) ----
sy = sp.symbols("one x1 x2 x3")
vec = sp.Matrix([1, sy[1], sy[2], sy[3]])
Msym = sp.Matrix([[sp.Rational(M[i][j].numerator, M[i][j].denominator) for j in range(n)] for i in range(n)])
quad_poly = sp.expand((vec.T * Msym * vec)[0])
sos = sum(sp.Rational(D[k].numerator, D[k].denominator) *
          (sum(sp.Rational(L[i][k].numerator, L[i][k].denominator)*vec[i] for i in range(n)))**2
          for k in range(n))
print(f"\nSOS/PSD Gram certificate (M = sum_k D_k v_k v_k^T) reconstructs the moment form exactly: "
      f"{sp.expand(quad_poly - sos) == 0}")
print("\n=== VERDICT: the SoS pseudo-expectation `0 <= pe(s^2)` IS the exact-rational PSD/SOS")
print("engine (LDL^T pivots >= 0 = SOS Gram) -- same shape as RH Weil/Jensen minors + BG SOS base.")
print("Three programs (RH zero-free, BG bulk-discharge, P-vs-NP SoS), one box-positivity/SOS engine.")
print("""
HONEST SCOPE (cf. the BG owner's caveat 1): this instance is EASY -- a satisfiable
3-XOR whose pe is a real measure, so PSD is automatic.  It demonstrates the ENGINE
(the shape reduces to exact PSD/SOS), not a hard result.  The hard P-vs-NP content is
the SoS degree LOWER BOUND: constructing a pe for an UNSAT expanding instance that
keeps the moment matrix PSD through degree d (the tight moment-SDP feasibility) --
exactly analogous to BG's open tight field-tau.  The engine certifies the atoms; the
hard construction is the open research.  conjecture1_proved = False.""")
