"""S11 core: exact-rational Galerkin + Hilbert-Schmidt tail data for the operator with kernel
P(|x - y|) on L^2([0, a]), P(v) = sum_i c_i v^i (c_i rational).  conjecture1_proved = False.

Math (see telperion/docs/ARCH_S11_NOTES.md):
  basis phi_j(x) = Legendre P_j(2x/a - 1), j < N (orthogonal, G = diag(a/(2j+1)));
  central formula, x in [0, a]:
    int_0^a |x-y|^i y^m dy = x^{i+m+1} sum_k C(i,k)(-1)^k/(m+k+1)
                             + sum_k C(i,k) (-x)^{i-k} (a^{m+k+1} - x^{m+k+1})/(m+k+1);
  u_j = T phi_j (explicit polynomial), C_jl = <phi_l, u_j>, U_jl = <u_j, u_l>,
  KK = int int P(|x-y|)^2, q^2 = KK - tr(G^-1 U)  (one-sided HS tail, p = sum phi_j (x) u_j / n_j),
  M = U - C G^-1 C  (exact cross coupling ||(I - Pi) T h||^2).
  For f = h + r (r orthogonal to V_N): <Tf,f> <= a*Ca + 2|r| sqrt(a*Ma) + q|r|^2,
  so  lam G - C - t M >= 0  and  q + 1/t <= lam  give  <Tf,f> <= lam |f|^2."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
from fractions import Fraction as F
from math import comb

def padd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def pscale(c, p): return [c * x for x in p]
def pmul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        if x:
            for j, y in enumerate(q):
                r[i + j] += x * y
    return r
def pint(p, q, a):
    """int_0^a p q"""
    s = F(0)
    for i, x in enumerate(p):
        if x:
            for j, y in enumerate(q):
                if y: s += x * y * a ** (i + j + 1) / (i + j + 1)
    return s

def legendre_shift(N, a):
    """P_j(2x/a - 1) as coefficient lists in x."""
    out = []
    for j in range(N):
        # P_j(t) = sum_k C(j,k) C(j+k,k) ((t-1)/2)^k ; (t-1)/2 = x/a - 1
        # shifted: P_j(2s-1) = sum_k (-1)^{j+k} C(j,k) C(j+k,k) s^k, s = x/a
        out.append([F((-1) ** (j + k) * comb(j, k) * comb(j + k, k)) / a ** k for k in range(j + 1)])
    return out

_Fcache = {}
def Fim(i, m, a):
    """coefficient list of x -> int_0^a |x-y|^i y^m dy on [0, a]."""
    key = (i, m, a)
    if key in _Fcache: return _Fcache[key]
    r = [F(0)] * (i + m + 2)
    r[i + m + 1] += sum(F(comb(i, k) * (-1) ** k, m + k + 1) for k in range(i + 1))
    for k in range(i + 1):
        c = F(comb(i, k) * (-1) ** (i - k), m + k + 1)
        r[i - k] += c * a ** (m + k + 1)
        r[i - k + m + k + 1] -= c
    _Fcache[key] = r
    return r

def Tpoly(c, phi, a):
    """T phi for kernel sum_i c_i |x-y|^i."""
    out = [F(0)]
    for i, ci in enumerate(c):
        if ci == 0: continue
        for m, pm in enumerate(phi):
            if pm == 0: continue
            out = padd(out, pscale(ci * pm, Fim(i, m, a)))
    return out

def data(c, N, a):
    phi = legendre_shift(N, a)
    u = [Tpoly(c, p, a) for p in phi]
    G = [F(a, 2 * j + 1) for j in range(N)]
    C = [[pint(phi[l], u[j], a) for l in range(N)] for j in range(N)]
    U = [[pint(u[j], u[l], a) for l in range(N)] for j in range(N)]
    c2 = pmul(c, c)
    one = Tpoly(c2, [F(1)], a)          # x -> int P(|x-y|)^2 dy
    KK = pint(one, [F(1)], a)
    q2 = KK - sum(U[j][j] / G[j] for j in range(N))
    M = [[U[j][l] - sum(C[j][m] * C[m][l] / G[m] for m in range(N)) for l in range(N)] for j in range(N)]
    return dict(phi=phi, u=u, G=G, C=C, U=U, KK=KK, q2=q2, M=M)
