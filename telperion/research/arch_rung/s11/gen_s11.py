"""S11 certificate generator: spectral certificates for Connes-Consani's operator K_I (kernel chi(y-x)).
Emits ArchS11_Data.lean (all numbers are only PROPOSED here; the Lean kernel re-checks every one with
`decide +kernel` in ArchS11_Cert*.lean).  conjecture1_proved = False.

Math (telperion/docs/ARCH_S11_NOTES.md).  On [0, a] the certified kernel is
    k(x, y) = pv E (|x - y| / a) + c0,     E_i = round(chiCo_i a^i)   (i < NE = 46),
so |k - chiPoly(y - x) - c0| <= dR(a) := sum_{i<67} |chiCo_i a^i - E_i|  on [0, a]^2  (kernel-checked).
Hat (s = x/a) objects on [0, 1]:
    Psi_m = hatT E (t^m)    : s -> int_0^1 pv E(|s-t|) t^m dt  (exact central formula),
    Phi_j = Legendre P_j(2s - 1),  U_j = sum_m Phi_jm Psi_m + c0 (int Phi_j) . 1   (= T^ Phi_j),
    rho_j = U_j - sum_l B_jl Phi_l   (B rounded; any B is sound),
    Q = lam G - C - t diag(dh),  G = mom(Phi, Phi), C = mom(U, Phi),
    dh_j >= |rho_j|^2 (sum al)/al_j  (weighted Cauchy-Schwarz on the residuals; exact LDL^T),
    q2 = int int k^2 - 2 sum_j w_j |U_j|^2 + sum_jj' w_j w_j' <Phi_j,Phi_j'> <U_j,U_j'>,  w_j = 2j + 1,
    and q^2 >= q2, q + 1/t <= lam.
Then for every f in L^2([0, a]):  re <T_k f, f> <= a lam |f|^2  (ArchS11_Galerkin).
Usage: python gen_s11.py OUTDIR"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import sys, time
from fractions import Fraction as F
from math import comb, factorial
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from chico import load

mp.mp.dps = 50
chiCo = load()                     # 67 exact rationals (S10's ArchS10.Data.chiCo)
NE = 46                            # truncation of the kernel polynomial
RD = 24                            # decimal rounding of E
N = 8                              # Galerkin dimension
D = NE + N                         # length of every lc output (Psi_m has length NE + m + 1 <= D)

# ---------------- Python replicas of the Lean definitions (must agree exactly) ----------------
def binom(n, k): return F(comb(n, k)) if 0 <= k <= n else F(0)
def sg(k): return F(1) if k % 2 == 0 else F(-1)
_A = {}
def Acoef(i, m):
    if (i, m) not in _A:
        _A[(i, m)] = sum((binom(i, k) * (sg(k) - sg(i - k)) / (m + k + 1) for k in range(i + 1)), F(0))
    return _A[(i, m)]
def Bcoef(i, m, k): return binom(i, k) * sg(i - k) / (m + k + 1)
def Fc(i, m, d):
    r = F(0)
    if d == i + m + 1: r += Acoef(i, m)
    if d <= i: r += Bcoef(i, m, i - d)
    return r
def getD(L, k): return L[k] if 0 <= k < len(L) else F(0)
def hatT(E, P):
    out = []
    for d in range(len(E) + len(P)):
        s = F(0)
        for i in range(len(E)):
            if getD(E, i) == 0: continue
            for m in range(len(P)):
                if getD(P, m) == 0: continue
                s += getD(E, i) * getD(P, m) * Fc(i, m, d)
        out.append(s)
    return out
def mom(p, q):
    return sum((getD(p, i) * getD(q, j) / (i + j + 1) for i in range(len(p)) for j in range(len(q))
                if p[i] != 0 and q[j] != 0), F(0))
def unitL(m): return [F(0)] * m + [F(1)]
def Jc(n): return F(2, (n + 1) * (n + 2))
def KKh(E, c0):
    s = sum((getD(E, i) * getD(E, j) * Jc(i + j) for i in range(len(E)) for j in range(len(E))), F(0))
    return s + 2 * c0 * sum((getD(E, i) * Jc(i) for i in range(len(E))), F(0)) + c0 * c0
def lc(cs, ps, Dl):
    return [sum((getD(cs, s) * getD(ps[s] if s < len(ps) else [], k) for s in range(len(cs))), F(0))
            for k in range(Dl)]

def legendre(j):
    return [F((-1) ** (j + k) * comb(j, k) * comb(j + k, k)) for k in range(j + 1)]
PHI = [legendre(j) for j in range(N)]
W = [F(2 * j + 1) for j in range(N)]

def rnd(x, R): return F(round(x * 10 ** R), 10 ** R)
def fl(x): return mp.mpf(x.numerator) / x.denominator

def Escale(a):
    E = [rnd(chiCo[i] * a ** i, RD) for i in range(NE)]
    dR = sum(abs(chiCo[i] * a ** i - E[i]) for i in range(NE)) + sum(abs(chiCo[i] * a ** i) for i in range(NE, 67))
    return E, dR

def up(x, sig=3):
    """a rational >= x with `sig` significant digits"""
    if x <= 0: return F(0)
    xf = fl(x) if isinstance(x, F) else mp.mpf(x)
    if not isinstance(x, F): x = F(str(mp.nstr(xf, 30)))
    e = int(mp.floor(mp.log10(xf))) - sig + 1
    q = F(10) ** e
    import math
    return F(math.ceil(x / q)) * q

def ldl(A):
    n = len(A); A = [row[:] for row in A]; out = []
    for s in range(n):
        d = A[s][s]
        if d < 0: return None
        if d == 0:
            if any(A[s][k] != 0 for k in range(s, n)): return None
            out.append((F(0), [F(0)] * n)); continue
        v = [F(0)] * s + [F(1)] + [A[s][k] / d for k in range(s + 1, n)]
        out.append((d, v))
        for j in range(s + 1, n):
            for k in range(s + 1, n):
                A[j][k] -= A[s][j] * A[s][k] / d
    return out

def cert(E, c0, lam_grid_start, step, tries=4000):
    t0 = time.time()
    Psi = [hatT(E, unitL(m)) for m in range(N)]
    U = [lc([getD(PHI[j], m) if m < N else c0 * mom(PHI[j], [F(1)]) for m in range(N + 1)], Psi + [[F(1)]], D)
         for j in range(N)]
    G = [[mom(PHI[j], PHI[l]) for l in range(N)] for j in range(N)]
    C = [[mom(U[j], PHI[l]) for l in range(N)] for j in range(N)]
    B = [[rnd(C[j][l] * (2 * l + 1), 30) for l in range(N)] for j in range(N)]
    rho = [lc([F(1)] + [-B[j][l] for l in range(N)], [U[j]] + PHI, D) for j in range(N)]
    rn2 = [mom(rho[j], rho[j]) for j in range(N)]
    al = [up(F(str(mp.nstr(mp.sqrt(mp.sqrt(fl(x))), 20))), 3) for x in rn2]
    sal = sum(al, F(0))
    dh = [up(rn2[j] * sal / al[j], 4) for j in range(N)]
    q2 = KKh(E, c0) - 2 * sum((W[j] * mom(U[j], U[j]) for j in range(N)), F(0)) \
        + sum((W[j] * W[l] * G[j][l] * mom(U[j], U[l]) for j in range(N) for l in range(N)), F(0))
    q = up(mp.sqrt(fl(q2)) * (1 + mp.mpf(10) ** -6), 4)
    while q * q < q2: q = q * F(10001, 10000)
    # galerkin top (hat)
    Cm = mp.matrix([[fl(x) for x in r] for r in C]); Gm = [fl(G[j][j]) for j in range(N)]
    Gs = mp.diag([1 / mp.sqrt(g) for g in Gm])
    mu = max(mp.eigsy(Gs * Cm * Gs)[0])
    lam = lam_grid_start
    for _ in range(tries):
        if lam > q:
            t = F(1) / (lam - q) * F(11, 10)          # t slightly above 1/(lam - q) leaves q + 1/t < lam
            Q = [[lam * G[j][l] - C[j][l] - (t * dh[j] if j == l else 0) for l in range(N)] for j in range(N)]
            L = ldl(Q)
            if L is not None and q + 1 / t <= lam:
                print("   cert: mu^=%.9f lam^=%s q^=%s t^=%s dmax^=%.3g (%.1fs)" % (mu, float(lam), float(q), float(t), float(max(dh)), time.time() - t0),
                      file=sys.stderr)
                return dict(E=E, c0=c0, Psi=Psi, U=U, B=B, rho=rho, Q=Q, L=L, lam=lam, t=t, q=q, q2=q2, mu=mu, al=al, dh=dh)
        lam += step
    raise RuntimeError("no certificate")

def testvec(E, c0):
    Psi = [hatT(E, unitL(m)) for m in range(N)]
    U = [lc([getD(PHI[j], m) if m < N else c0 * mom(PHI[j], [F(1)]) for m in range(N + 1)], Psi + [[F(1)]], D)
         for j in range(N)]
    C = [[fl(mom(U[j], PHI[l])) for l in range(N)] for j in range(N)]
    G = [fl(mom(PHI[j], PHI[j])) for j in range(N)]
    Gs = mp.diag([1 / mp.sqrt(g) for g in G])
    ev, V = mp.eigsy(Gs * mp.matrix(C) * Gs)
    k = max(range(N), key=lambda i: ev[i])
    coef = [rnd(F(str(mp.nstr(V[j, k] / mp.sqrt(G[j]), 40))), 30) for j in range(N)]   # Legendre coefficients
    ut = [sum((coef[j] * getD(PHI[j], m) for j in range(N)), F(0)) for m in range(N)]  # monomial coefficients
    Ut = lc(ut, Psi, D)
    ray = mom(Ut, ut) / mom(ut, ut)
    return dict(Psi=Psi, ut=ut, Ut=Ut, ray=ray)

# ---------------- Lean emission ----------------
def qlean(x):
    x = F(x)
    return "(%d : ℚ)" % x.numerator if x.denominator == 1 else "(%d / %d : ℚ)" % (x.numerator, x.denominator)
def qlist(L): return "[" + ", ".join(qlean(x) for x in L) + "]"
def qlist2(LL): return "[" + ",\n    ".join(qlist(L) for L in LL) + "]"
def ldllean(L): return "[" + ",\n    ".join("(%s, %s)" % (qlean(d), qlist(v)) for d, v in L) + "]"

HEADER = r'''/-
  ArchS11_Data -- GENERATED by telperion/research/arch_rung/s11/gen_s11.py (do not edit).
  Exact-rational data of the spectral certificates for CC's operator K_I (stage S11).
  Every inequality and identity below is re-checked by the kernel (`decide +kernel`, ArchS11_Cert*.lean).
  conjecture1_proved = False.
-/
import ArchS10_Data

namespace ArchS11.Data

open Finset

set_option maxHeartbeats 0

/-! ## A. Generic computable definitions. -/

/-- Pascal's triangle, rows `0 .. 45` (checked against the recurrence in `binOK`). -/
def binL : List (List ℕ) := %BINL%
def binN (n k : ℕ) : ℕ := (binL.getD n []).getD k 0
def binom (n k : ℕ) : ℚ := (binN n k : ℚ)
def sg (k : ℕ) : ℚ := if k % 2 = 0 then 1 else -1
/-- The coefficient of `s^{i+m+1}` in `∫_0^1 |s - t|^i t^m dt`. -/
def Acoef (i m : ℕ) : ℚ :=
  ∑ k ∈ range (i + 1), binom i k * (sg k - sg (i - k)) / ((m + k + 1 : ℕ) : ℚ)
def Bcoef (i m k : ℕ) : ℚ := binom i k * sg (i - k) / ((m + k + 1 : ℕ) : ℚ)
/-- The coefficient of `s^d` in `∫_0^1 |s - t|^i t^m dt` (`s ∈ [0, 1]`). -/
def Fc (i m d : ℕ) : ℚ :=
  (if d = i + m + 1 then Acoef i m else 0) + (if d ≤ i then Bcoef i m (i - d) else 0)
/-- Coefficients of `s ↦ ∫_0^1 pv E (|s - t|) · pv P t dt` on `[0, 1]`. -/
def hatT (E P : List ℚ) : List ℚ :=
  (List.range (E.length + P.length)).map fun d =>
    ∑ i ∈ range E.length, if E.getD i 0 = 0 then 0 else
      ∑ m ∈ range P.length, if P.getD m 0 = 0 then 0 else E.getD i 0 * P.getD m 0 * Fc i m d
/-- `∫_0^1 pv p · pv q`. -/
def mom (p q : List ℚ) : ℚ :=
  ∑ i ∈ range p.length, ∑ j ∈ range q.length, p.getD i 0 * q.getD j 0 / ((i + j + 1 : ℕ) : ℚ)
def unitL (m : ℕ) : List ℚ := List.replicate m 0 ++ [1]
/-- `∫_0^1 ∫_0^1 |s - t|^n = 2 / ((n + 1)(n + 2))`. -/
def Jc (n : ℕ) : ℚ := 2 / (((n + 1) * (n + 2) : ℕ) : ℚ)
/-- `∫_0^1 ∫_0^1 (pv E (|s - t|) + c0)^2`. -/
def KKh (E : List ℚ) (c0 : ℚ) : ℚ :=
  (∑ i ∈ range E.length, ∑ j ∈ range E.length, E.getD i 0 * E.getD j 0 * Jc (i + j))
    + 2 * c0 * (∑ i ∈ range E.length, E.getD i 0 * Jc i) + c0 * c0
/-- The linear combination `Σ_s cs_s · ps_s`, as a coefficient list of length `D`. -/
def lc (cs : List ℚ) (ps : List (List ℚ)) (D : ℕ) : List ℚ :=
  (List.range D).map fun k => ∑ s ∈ range cs.length, cs.getD s 0 * (ps.getD s []).getD k 0
def mget (A : List (List ℚ)) (j k : ℕ) : ℚ := (A.getD j []).getD k 0
/-- `A = Σ_s d_s v_s v_sᵀ` on `n × n`, every `d_s ≥ 0` (an `LDLᵀ` certificate given as data). -/
def ldlOK (A : List (List ℚ)) (L : List (ℚ × List ℚ)) (n : ℕ) : Bool :=
  L.all (fun p => decide (0 ≤ p.1)) &&
  (List.range n).all (fun j => (List.range n).all (fun k =>
    decide (mget A j k = (L.map (fun p => p.1 * p.2.getD j 0 * p.2.getD k 0)).sum)))

def binOK : Bool :=
  (List.range 47).all (fun n => decide ((binL.getD n []).length = n + 1) && decide (binN n 0 = 1)) &&
  (List.range 46).all (fun n => (List.range (n + 1)).all fun k =>
    decide (binN (n + 1) (k + 1) = binN n k + binN n (k + 1)))

/-! ## B. Parameters. -/

/-- Galerkin dimension. -/
def NG : ℕ := %N%
/-- Length of the kernel polynomial `E` (degrees `0 .. 45`). -/
def NE : ℕ := %NE%
/-- Length of every combined coefficient list. -/
def DL : ℕ := %D%
/-- Legendre polynomials `P_j(2s - 1)`, `j < NG`, in the monomial basis. -/
def PhiL : List (List ℚ) := %PHI%
def Phi (j : ℕ) : List ℚ := PhiL.getD j []
/-- HS-tail weights. -/
def wq (j : ℕ) : ℚ := 2 * (j : ℚ) + 1

/-- The coefficient vector of `U_j = Σ_m Phi_jm Psi_m + c0 (∫ Phi_j) · 1` against `Psi ++ [[1]]`. -/
def ucoef (c0 : ℚ) (j : ℕ) : List ℚ :=
  (List.range (NG + 1)).map fun m => if m < NG then (Phi j).getD m 0 else c0 * mom (Phi j) [1]

/-- The S10 rounding: `Σ_{i<67} |chiCo_i a^i - E_i| ≤ dR`. -/
def roundOK (E : List ℚ) (a dR : ℚ) : Bool :=
  decide (E.length = NE) &&
  decide ((∑ i ∈ range ArchS10.Data.NP, |ArchS10.Data.chiCo i * a ^ i - E.getD i 0|) ≤ dR)

def psiOK (E : List ℚ) (Psi : List (List ℚ)) : Bool :=
  decide (Psi.length = NG) && (List.range NG).all fun m => decide (hatT E (unitL m) = Psi.getD m [])

def uOK (Psi : List (List ℚ)) (c0 : ℚ) (U : List (List ℚ)) : Bool :=
  decide (U.length = NG) &&
  (List.range NG).all fun j => decide (U.getD j [] = lc (ucoef c0 j) (Psi ++ [[1]]) DL)

def rhoOK (U B rho : List (List ℚ)) : Bool :=
  decide (rho.length = NG) &&
  (List.range NG).all fun j =>
    decide (rho.getD j [] = lc (1 :: (List.range NG).map fun l => -mget B j l) (U.getD j [] :: PhiL) DL)

/-- The Legendre Gram matrix is diagonal with positive entries. -/
def orthoOK : Bool :=
  (List.range NG).all fun j => (List.range NG).all fun l =>
    if j = l then decide (0 < mom (Phi j) (Phi j)) else decide (mom (Phi j) (Phi l) = 0)

/-- The diagonal residual bound (weighted Cauchy-Schwarz, weights `al_j > 0`):
`|rho_j|² · (Σ_k al_k) / al_j ≤ dh_j`. -/
def dOK (rho : List (List ℚ)) (al dh : List ℚ) : Bool :=
  (List.range NG).all fun j => decide (0 < al.getD j 0) &&
    decide (mom (rho.getD j []) (rho.getD j []) * (∑ k ∈ range NG, al.getD k 0) / al.getD j 0
      ≤ dh.getD j 0)

def qmatOK (U Q : List (List ℚ)) (dh : List ℚ) (lam t : ℚ) : Bool :=
  (List.range NG).all fun j => (List.range NG).all fun l =>
    decide (mget Q j l = lam * mom (Phi j) (Phi l) - mom (U.getD j []) (Phi l)
      - (if j = l then t * dh.getD j 0 else 0))

def q2val (E : List ℚ) (c0 : ℚ) (U : List (List ℚ)) : ℚ :=
  KKh E c0 - 2 * (∑ j ∈ range NG, wq j * mom (U.getD j []) (U.getD j []))
    + ∑ j ∈ range NG, ∑ l ∈ range NG,
        if mom (Phi j) (Phi l) = 0 then 0 else
          wq j * wq l * mom (Phi j) (Phi l) * mom (U.getD j []) (U.getD l [])

def tailOK (E : List ℚ) (c0 : ℚ) (U : List (List ℚ)) (lam t q : ℚ) : Bool :=
  decide (0 < t) && decide (0 ≤ q) && decide (q + 1 / t ≤ lam) && decide (q2val E c0 U ≤ q * q)

def lenOK (Psi : List (List ℚ)) : Bool :=
  (List.range NG).all fun m => decide ((Psi.getD m []).length ≤ DL)

'''

def main():
    outdir = sys.argv[1]
    out = []
    w = out.append
    binl = "[" + ", ".join("[" + ", ".join(str(comb(i, k)) for k in range(i + 1)) + "]" for i in range(47)) + "]"
    w(HEADER.replace("%BINL%", binl).replace("%N%", str(N)).replace("%NE%", str(NE)).replace("%D%", str(D))
      .replace("%PHI%", qlist2(PHI)))
    report = {}
    scales = {
        "A": F(1, 2),                       # T1: |I| = 1/2
        "H": F(6931471808, 10 ** 10),       # T2 upper: H >= log 2 (Real.log_two_lt_d9)
        "L": F(6931471803, 10 ** 10),       # T2 lower: lo <= log 2 (Real.log_two_gt_d9)
    }
    Es = {}
    for key, a in scales.items():
        E, dR = Escale(a)
        dRq = up(dR, 3)
        Es[key] = (E, dRq)
        print("scale %s: a = %s  dR = %.3g" % (key, float(a), float(dRq)), file=sys.stderr)
        w("/-! ## Scale %s : a = %s. -/" % (key, a))
        w("def a%s : ℚ := %s" % (key, qlean(a)))
        w("def E%s : List ℚ := %s" % (key, qlist(E)))
        w("def dR%s : ℚ := %s" % (key, qlean(dRq)))
        Psi = [hatT(E, unitL(m)) for m in range(N)]
        w("def Psi%s : List (List ℚ) := %s" % (key, qlist2(Psi)))
        w("")
    # certificates: (name, scale, c0, lambda-hat start, step)
    aA, aH, aL = scales["A"], scales["H"], scales["L"]
    certs = [
        ("T1", "A", F(0), F(95920, 100000) / aA, F(1, 10 ** 6) / aA),
        ("Top", "H", F(0), F(105156, 100000) / aH, F(1, 10 ** 6) / aH),
        ("Gam", "H", -F(58, 1000) / aH, F(99930, 100000) / aH, F(1, 10 ** 6) / aH),
        ("Lam2", "H", -F(1) / aH, F(68650, 100000) / aH, F(1, 10 ** 6) / aH),
        ("Ovl", "H", -F(2, 100) / aH, F(103348, 100000) / aH, F(1, 10 ** 6) / aH),
    ]
    for name, key, c0, lam0, step in certs:
        E, dRq = Es[key]
        a = scales[key]
        print("cert %s (scale %s, c0 = %s):" % (name, key, float(c0)), file=sys.stderr)
        c = cert(E, c0, lam0, step)
        # round lam up to a clean rational with 7 significant digits in real units
        w("/-! ## Certificate %s (scale %s). -/" % (name, key))
        w("def c0%s : ℚ := %s" % (name, qlean(c0)))
        w("def U%s : List (List ℚ) := %s" % (name, qlist2(c["U"])))
        w("def B%s : List (List ℚ) := %s" % (name, qlist2(c["B"])))
        w("def rho%s : List (List ℚ) := %s" % (name, qlist2(c["rho"])))
        w("def Q%s : List (List ℚ) := %s" % (name, qlist2(c["Q"])))
        w("def L%s : List (ℚ × List ℚ) := %s" % (name, ldllean(c["L"])))
        w("def lam%s : ℚ := %s" % (name, qlean(c["lam"])))
        w("def t%s : ℚ := %s" % (name, qlean(c["t"])))
        w("def q%s : ℚ := %s" % (name, qlean(c["q"])))
        w("def al%s : List ℚ := %s" % (name, qlist(c["al"])))
        w("def dh%s : List ℚ := %s" % (name, qlist(c["dh"])))
        w("def ok%s : Bool :=" % name)
        w("  uOK Psi%s c0%s U%s && rhoOK U%s B%s rho%s && dOK rho%s al%s dh%s && qmatOK U%s Q%s dh%s lam%s t%s &&"
          % (key, name, name, name, name, name, name, name, name, name, name, name, name, name))
        w("  ldlOK Q%s L%s NG && tailOK E%s c0%s U%s lam%s t%s q%s"
          % (name, name, key, name, name, name, name, name))
        w("")
        report[name] = (key, a, c0, c["lam"], c["mu"], c["q"], dRq)
    # test vectors
    for name, key in [("T1lo", "A"), ("Toplo", "L")]:
        E, dRq = Es[key]
        tv = testvec(E, F(0))
        lamlo = F(int(fl(tv["ray"]) * 10 ** 7) - 1, 10 ** 7)     # hat lower bound, rounded down
        assert tv["ray"] >= lamlo
        w("/-! ## Test vector %s (scale %s). -/" % (name, key))
        w("def ut%s : List ℚ := %s" % (name, qlist(tv["ut"])))
        w("def Ut%s : List ℚ := %s" % (name, qlist(tv["Ut"])))
        w("def lam%s : ℚ := %s" % (name, qlean(lamlo)))
        w("def ok%s : Bool :=" % name)
        w("  decide (ut%s.length = NG) && decide (Ut%s = lc ut%s Psi%s DL) &&" % (name, name, name, key))
        w("  decide (0 < mom ut%s ut%s) && decide (lam%s * mom ut%s ut%s ≤ mom Ut%s ut%s)"
          % (name, name, name, name, name, name, name))
        w("")
        report[name] = (key, scales[key], lamlo, dRq)
    w("end ArchS11.Data")
    open(os.path.join(outdir, "ArchS11_Data.lean"), "w").write("\n".join(out) + "\n")
    # summary in real units
    dChi = F(141, 10 ** 9)
    print("\nSUMMARY (real units; true kernel adds a*(dChi + dR)):", file=sys.stderr)
    for name, v in report.items():
        if len(v) == 7:
            key, a, c0, lam, mu, q, dRq = v
            print("  %-5s a=%.10f c0*a=%.4f  lam*a=%.8f  (galerkin %.8f)  +pert %.2e" %
                  (name, float(a), float(-c0 * a), float(lam * a), float(mu * a), float(a * (dChi + dRq))), file=sys.stderr)
        else:
            key, a, lamlo, dRq = v
            print("  %-5s a=%.10f  lower lam*a=%.8f  -pert %.2e" % (name, float(a), float(lamlo * a), float(a * (dChi + dRq))), file=sys.stderr)

if __name__ == "__main__":
    main()
