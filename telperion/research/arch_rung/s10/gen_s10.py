"""S10 certificate generator: certified enclosure of Connes-Consani's kernel chi on [0, log 2].
Emits ArchS10_Data.lean (all numbers are only PROPOSED here; every inequality is re-checked by the
Lean kernel with `decide +kernel`).

Math (see telperion/docs/ARCH_S10_NOTES.md):
  * head n <= 12: with S9's psi_n (degree 78, rational) and theta_n, the model of
      w_n C_n(t) is  W_n * sum_l hh_{n,l} (e^{b_l t} - e^{-b_l t}),  b_l = 2l + 1/2,
      W_n = theta_n^2/(1 - theta_n^2),
      hh_{n,l} = sum_k 4kl B_k B_l/(2k+2l+1) - psi_n(1) 2l B_l       (exact polynomial integral);
    d_l = sum_n W_n hh_{n,l} is rounded entrywise (Dz / 10^P2).
  * tail n > 12: Bessel over the orthonormal eigenfamily, through S9's rank-40 frame:
      sum_{n in S} (T phi_n (w))^2 <= Abnd(Psi, zeta, c)   (weighted Cauchy-Schwarz, weights c).
  * polynomial: P(t) = sum_{l<L0} d_l (T_N(b_l t) - T_N(-b_l t)), T_N = exp Taylor polynomial;
    remainder by Complex.exp_bound' (needs b_l log2 <= (N+1)/2), dropped l >= L0 by 2^{2l+1}+1.
conjecture1_proved = False.
Usage: python gen_s10.py OUT.lean"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import re, sys, math
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
S9DATA = os.path.join(HERE, "../../../examples/rvm_bridge/lean/ArchS9_Data.lean")
src = open(S9DATA).read()

def intlist(name):
    m = re.search(r"^def %s : List ℤ := \[([^\]]*)\]" % name, src, re.M)
    return [int(x) for x in m.group(1).split(",")]

def qconst(name):
    m = re.search(r"^def %s : ℚ := \((-?\d+) / (\d+) : ℚ\)" % name, src, re.M)
    return F(int(m.group(1)), int(m.group(2)))

def qlist(name):
    m = re.search(r"^def %s : List ℚ := \[(.*)\]$" % name, src, re.M)
    return [F(int(a), int(b)) for a, b in re.findall(r"\((-?\d+) / (\d+) : ℚ\)", m.group(1))]

J, NC = 40, 12
NH = NC + 1
DB, DT = 10 ** 80, 10 ** 160
Lc = int(re.search(r"^def Lc : ℕ := (\d+)", src, re.M).group(1))
Bz = [intlist("rB%d" % n) for n in range(J)]
Tz = intlist("tabT")
th = [F(Tz[n], DT) for n in range(J)]
Bq = [[F(Bz[n][k], DB) for k in range(J)] for n in range(J)]
w2 = qlist("w2L"); V = qlist("VL"); Vd = qlist("VdL")
gam = qconst("gamQ")
rho = None
zeta1, zeta2, zetad2 = qconst("zeta1Q"), qconst("zeta2Q"), qconst("zetad2Q")
d0 = qconst("d0Q")
if rho is None:
    # rhoQ lives in ArchS9_CertRes.lean
    rsrc = open(os.path.join(HERE, "../../../examples/rvm_bridge/lean/ArchS9_CertRes.lean")).read()
    m = re.search(r"def rhoQ : ℚ := \(?(-?\d+) / (\d+)", rsrc)
    rho = F(int(m.group(1)), int(m.group(2)))

def up(x, sig=3):
    """Round a positive Fraction UP to `sig` significant digits (returns Fraction)."""
    x = F(x)
    assert x >= 0
    if x == 0:
        return F(0)
    e = math.floor(math.log10(x.numerator) - math.log10(x.denominator)) - sig + 1
    s = F(10) ** e
    q = -((-x) // s)
    return q * s

def qlean(q):
    q = F(q)
    return "(%d / %d : ℚ)" % (q.numerator, q.denominator)

def fl(q):
    return float(q)

# ---------------- head: hh, W, D -----------------
def Wz(d):
    assert Lc % (2 * d + 1) == 0
    return Lc // (2 * d + 1)

hhz = [[sum(4 * k * l * Bz[n][k] * Bz[n][l] * Wz(k + l) for k in range(J))
        - sum(Bz[n]) * (2 * l) * Bz[n][l] * Lc for l in range(J)] for n in range(NH)]
hh = [[F(hhz[n][l], DB * DB * Lc) for l in range(J)] for n in range(NH)]
Wth = [th[n] ** 2 / (1 - th[n] ** 2) for n in range(NH)]
P2 = 60
DD = 10 ** P2
Dz = [[round(Wth[n] * hh[n][l] * DD) for l in range(J)] for n in range(NH)]
eD = F(1, DD)          # |W hh - Dz/DD| <= 1/(2 DD) < eD
for n in range(NH):
    for l in range(J):
        assert abs(Wth[n] * hh[n][l] - F(Dz[n][l], DD)) <= eD
dq = [sum(F(Dz[n][l], DD) for n in range(NH)) for l in range(J)]

# eps'(1+) head
psi1 = [sum(Bq[n]) for n in range(J)]
Eexact = sum(Wth[n] * psi1[n] ** 2 for n in range(NH))
PE = 40
EQ = F(round(Eexact * 10 ** PE), 10 ** PE)
eEQ = F(1, 10 ** PE)
assert abs(Eexact - EQ) <= eEQ

# ---------------- head perturbation constants -----------------
PsiQ = [sum(abs(Bq[m][k]) * 4 ** k for k in range(J)) for m in range(J)]
PsidQ = [sum(abs(Bq[m][k]) * (2 * k) * F(2) ** (2 * k - 1) for k in range(1, J)) for m in range(J)]
Psi1Q = [sum(abs(Bq[m][k]) for k in range(J)) for m in range(J)]

def headErr(n):
    t = abs(th[n]); e0, e1, ww = V[n], Vd[n], w2[n]
    G0, G1 = t * PsiQ[n], t * PsidQ[n]
    lo = 1 - (t + ww) ** 2
    assert lo > 0
    Bnd = 4 * (e1 * (G1 + e1) + G1 * e1) + (e1 * (G0 + e0) + G1 * e0) + 4 * (e0 * (G1 + e1) + G0 * e1)
    return Bnd / lo + (4 * G1 ** 2 + 5 * G0 * G1) * (ww * (2 * t + ww)) / (lo * (1 - th[n] ** 2))

def epsErr(n):
    t = abs(th[n]); e0, ww = V[n], w2[n]
    g = abs(th[n] * psi1[n])
    lo = 1 - (t + ww) ** 2
    return e0 * (2 * g + e0) / lo + g ** 2 * (ww * (2 * t + ww)) / (lo * (1 - th[n] ** 2))

errH = [up(headErr(n)) for n in range(NH)]
errE = [up(epsErr(n)) for n in range(NH)]

# ---------------- tail -----------------
def Aterms(Psi, z):
    ts = []
    for m in range(J):
        if m <= NC:
            ts.append(th[m] ** 2 * Psi[m] ** 2 * rho ** 2 / (abs(th[m]) - d0) ** 2)
        else:
            ts.append(th[m] ** 2 * Psi[m] ** 2 * (1 + gam))
    ts.append(z ** 2)
    return ts

def isqrt_frac(x):
    """approximate sqrt of a Fraction as a Fraction with ~4 sig digits (any positive value is sound)."""
    v = math.sqrt(float(x)) if float(x) > 0 else 0.0
    if v < 1e-150:
        return F(1, 10 ** 150)
    e = math.floor(math.log10(v)) - 3
    return F(max(1, round(v / 10 ** e)) * 10 ** max(e, 0), 10 ** max(-e, 0))

def Abnd(Psi, z, c):
    ts = Aterms(Psi, z)
    return sum(c) * sum(ts[i] / c[i] for i in range(J + 1))

cA = [isqrt_frac(x) for x in Aterms(PsiQ, zeta2)]
cAd = [isqrt_frac(x) for x in Aterms(PsidQ, zetad2)]
cA1 = [isqrt_frac(x) for x in Aterms(Psi1Q, zeta1)]
AQ = up(Abnd(PsiQ, zeta2, cA)); AdQ = up(Abnd(PsidQ, zetad2, cAd)); A1Q = up(Abnd(Psi1Q, zeta1, cA1))
tauQ = up((4 * AdQ + (AdQ + AQ) / 2 + 2 * (AQ + AdQ)) / (1 - d0 ** 2))
tauE = up(A1Q / (1 - d0 ** 2))

# ---------------- polynomial -----------------
bQ = F(6931471808, 10 ** 10)          # Mathlib: log 2 < 0.6931471808
def bet(l): return F(4 * l + 1, 2)
def remP(L0, N):
    s = sum(abs(dq[l]) * 4 * (bet(l) * bQ) ** N / math.factorial(N) for l in range(L0))
    s += sum(abs(dq[l]) * (2 ** (2 * l + 1) + 1) for l in range(L0, J))
    return s
TARGET_P = F(2, 10 ** 8)
best = None
for L0 in range(10, J + 1):
    Nmin = math.ceil(2 * bet(L0 - 1) * bQ - 1)
    for N in range(max(Nmin, 2), 200, 2):
        r = remP(L0, N)
        if r <= TARGET_P:
            if best is None or N < best[1]:
                best = (L0, N, r)
            break
L0, NP, rP = best
deltaP = up(rP)
pco = [sum(dq[l] * (bet(l) ** i - (-bet(l)) ** i) / math.factorial(i) for l in range(L0)) for i in range(NP)]
Pmax = up(sum(abs(pco[i]) * bQ ** i for i in range(NP)))

# ---------------- totals -----------------
sumH = sum(errH)
roundQ = sum(NH * eD * (2 ** (2 * l + 1) + 1) for l in range(J))
dQtot = up(sumH + roundQ + tauQ)
deltaE = up(sum(errE) + eEQ + tauE)
Elo = EQ - deltaE
assert Elo > 0
chiErr = (dQtot + deltaP) / (2 * Elo) + Pmax * deltaE / (2 * Elo * EQ)
deltaChi = up(chiErr)

print("eps'(1+) =", float(EQ), " deltaE =", float(deltaE), file=sys.stderr)
print("head errH max =", max(fl(x) for x in errH), " errE max =", max(fl(x) for x in errE), file=sys.stderr)
print("A =", fl(AQ), " A' =", fl(AdQ), " A1 =", fl(A1Q), " tauQ =", fl(tauQ), " tauE =", fl(tauE), file=sys.stderr)
print("poly L0 =", L0, " N =", NP, " deltaP =", fl(deltaP), " Pmax =", fl(Pmax), file=sys.stderr)
print("dQtot =", fl(dQtot), " deltaChi =", fl(deltaChi), file=sys.stderr)

# sanity: evaluate chi from poly against direct sinh sum
import mpmath as mp
mp.mp.dps = 60
def Fsum(t):
    return sum(mp.mpf(dq[l].numerator) / dq[l].denominator * 2 * mp.sinh((2 * l + mp.mpf(1) / 2) * t) for l in range(J))
def Ppoly(t):
    return sum(mp.mpf(pco[i].numerator) / pco[i].denominator * mp.mpf(t) ** i for i in range(NP))
mx = 0
for k in range(0, 101):
    t = mp.log(2) * k / 100
    mx = max(mx, abs(Fsum(t) - Ppoly(t)))
print("sampled |F - P| max =", mp.nstr(mx, 5), file=sys.stderr)

# ---------------- emit -----------------
out = []
w = out.append
w("/-")
w("  ArchS10_Data -- GENERATED by telperion/research/arch_rung/s10/gen_s10.py (do not edit).")
w("  Proposed constants for the certified enclosure of CC's kernel chi on [0, log 2] (stage S10).")
w("  Every inequality is re-checked by the kernel (ArchS10_Cert*.lean).  conjecture1_proved = False.")
w("-/")
w("import ArchS9_Data")
w("import ArchS9_CertRes")
w("")
w("namespace ArchS10.Data")
w("")
w("open Finset ArchS9.Data")
w("")
w("set_option maxHeartbeats 0")
w("")
w("/-- Number of certified head prolates (n = 0 .. 12). -/")
w("def NH : ℕ := %d" % NH)
w("def DD : ℕ := 10 ^ %d" % P2)
for n in range(NH):
    w("def rD%d : List ℤ := [%s]" % (n, ", ".join(str(x) for x in Dz[n])))
w("def tabD : List (List ℤ) := [%s]" % ", ".join("rD%d" % n for n in range(NH)))
w("def Dz (n l : ℕ) : ℤ := (tabD.getD n []).getD l 0")
w("/-- `Dq n l ≈ θ_n²/(1-θ_n²) · hh_{n,l}`. -/")
w("def Dq (n l : ℕ) : ℚ := (Dz n l : ℚ) / (DD : ℚ)")
w("/-- The coefficients of the head kernel: `Qε_head(t) ≈ Σ_l dq l (e^{b_l t} - e^{-b_l t})`. -/")
w("def dq (l : ℕ) : ℚ := ∑ n ∈ range NH, Dq n l")
w("def eDQ : ℚ := %s" % qlean(eD))
w("/-- The exact polynomial-integral coefficients, as integers over `DB² Lc`. -/")
w("def hhz (n l : ℕ) : ℤ := (∑ k ∈ range Jd, 4 * (k : ℤ) * l * Bz n k * Bz n l * Wz (k + l))")
w("  - (∑ k ∈ range Jd, Bz n k) * (2 * l) * Bz n l * (Lc : ℤ)")
w("def hhq (n l : ℕ) : ℚ := (hhz n l : ℚ) / ((DB : ℚ) ^ 2 * (Lc : ℚ))")
w("def Wthq (n : ℕ) : ℚ := thq n ^ 2 / (1 - thq n ^ 2)")
w("def roundRowOK (n : ℕ) : Bool :=")
w("  (List.range Jd).all fun l => decide (|Wthq n * hhq n l - Dq n l| ≤ eDQ)")
w("")
w("/-- ψ_n(1). -/")
w("def psi1q (n : ℕ) : ℚ := ∑ k ∈ range Jd, Bq n k")
w("def EQ : ℚ := %s" % qlean(EQ))
w("def eEQ : ℚ := %s" % qlean(eEQ))
w("def epsHeadOK : Bool := decide (|(∑ n ∈ range NH, Wthq n * psi1q n ^ 2) - EQ| ≤ eEQ)")
w("")
w("/-! Head perturbation constants. -/")
w("def Psid1Q (m : ℕ) : ℚ := ∑ k ∈ range Jd, |Bq m k| * (2 * k : ℚ)")
w("def G0q (n : ℕ) : ℚ := |thq n| * PsiQ n")
w("def G1q (n : ℕ) : ℚ := |thq n| * PsidQ n")
w("def loq (n : ℕ) : ℚ := 1 - (|thq n| + w2q n) ^ 2")
w("def bndq (n : ℕ) : ℚ :=")
w("  4 * (Vdq n * (G1q n + Vdq n) + G1q n * Vdq n) + (Vdq n * (G0q n + Vq n) + G1q n * Vq n)")
w("    + 4 * (Vq n * (G1q n + Vdq n) + G0q n * Vdq n)")
w("def errHL : List ℚ := [%s]" % ", ".join(qlean(x) for x in errH))
w("def errHq (n : ℕ) : ℚ := errHL.getD n 0")
w("def errEL : List ℚ := [%s]" % ", ".join(qlean(x) for x in errE))
w("def errEq (n : ℕ) : ℚ := errEL.getD n 0")
w("def gq (n : ℕ) : ℚ := |thq n * psi1q n|")
w("def headOK : Bool := (List.range NH).all fun n =>")
w("  decide (0 < loq n) && decide (thq n ^ 2 < 1) &&")
w("  decide (bndq n / loq n + (4 * G1q n ^ 2 + 5 * G0q n * G1q n) * (w2q n * (2 * |thq n| + w2q n))")
w("      / (loq n * (1 - thq n ^ 2)) ≤ errHq n) &&")
w("  decide (Vq n * (2 * gq n + Vq n) / loq n + gq n ^ 2 * (w2q n * (2 * |thq n| + w2q n))")
w("      / (loq n * (1 - thq n ^ 2)) ≤ errEq n)")
w("")
w("/-! Tail (Bessel through the rank-40 frame). -/")
def emit_list(name, xs):
    w("def %sL : List ℚ := [%s]" % (name, ", ".join(qlean(x) for x in xs)))
    w("def %s (i : ℕ) : ℚ := %sL.getD i 0" % (name, name))
emit_list("cA", cA); emit_list("cAd", cAd); emit_list("cA1", cA1)
w("/-- The weighted Cauchy-Schwarz + Bessel bound for `Σ_{n∈S} (T φ_n ω)²`. -/")
w("def Abnd (Ψ : ℕ → ℚ) (ζ : ℚ) (c : ℕ → ℚ) : ℚ :=")
w("  (∑ i ∈ range (Jd + 1), c i) *")
w("    ((∑ m ∈ range Jd, (if m ≤ NCw then thq m ^ 2 * Ψ m ^ 2 * rhoQ ^ 2 / ((|thq m| - d0Q) ^ 2 * c m)")
w("        else thq m ^ 2 * Ψ m ^ 2 * (1 + gamQ) / c m)) + ζ ^ 2 / c Jd)")
w("def AQ : ℚ := %s" % qlean(AQ))
w("def AdQ : ℚ := %s" % qlean(AdQ))
w("def A1Q : ℚ := %s" % qlean(A1Q))
w("def tauQ : ℚ := %s" % qlean(tauQ))
w("def tauE : ℚ := %s" % qlean(tauE))
w("def tailOK : Bool :=")
w("  ((List.range (Jd + 1)).all fun i => decide (0 < cA i) && decide (0 < cAd i) && decide (0 < cA1 i)) &&")
w("  ((List.range (NCw + 1)).all fun m => decide (d0Q < |thq m|)) &&")
w("  decide (Abnd PsiQ zeta2Q cA ≤ AQ) && decide (Abnd PsidQ zetad2Q cAd ≤ AdQ) &&")
w("  decide (Abnd Psi1Q zeta1Q cA1 ≤ A1Q) && decide (d0Q < 1) &&")
w("  decide ((4 * AdQ + (AdQ + AQ) / 2 + 2 * (AQ + AdQ)) / (1 - d0Q ^ 2) ≤ tauQ) &&")
w("  decide (A1Q / (1 - d0Q ^ 2) ≤ tauE)")
w("")
w("/-! The polynomial. -/")
w("def L0 : ℕ := %d" % L0)
w("def NP : ℕ := %d" % NP)
w("def bQ : ℚ := %s" % qlean(bQ))
w("def bet (l : ℕ) : ℚ := (4 * l + 1) / 2")
w("/-- Coefficients of `P(t) = Σ_{i<NP} pco i t^i ≈ Qε(t)` on `[0, log 2]`. -/")
w("def pco (i : ℕ) : ℚ := ∑ l ∈ range L0, dq l * (bet l ^ i - (-bet l) ^ i) / (i.factorial : ℚ)")
w("def deltaP : ℚ := %s" % qlean(deltaP))
w("def Pmax : ℚ := %s" % qlean(Pmax))
w("def polyOK : Bool :=")
w("  ((List.range L0).all fun l => decide (bet l * bQ ≤ ((NP : ℚ) + 1) / 2)) &&")
w("  decide ((∑ l ∈ range L0, |dq l| * 4 * (bet l * bQ) ^ NP / (NP.factorial : ℚ))")
w("    + (∑ l ∈ range (Jd - L0), |dq (L0 + l)| * (2 ^ (2 * (L0 + l) + 1) + 1)) ≤ deltaP) &&")
w("  decide ((∑ i ∈ range NP, |pco i| * bQ ^ i) ≤ Pmax)")
w("")
w("/-! Totals. -/")
w("def dQtot : ℚ := %s" % qlean(dQtot))
w("def deltaE : ℚ := %s" % qlean(deltaE))
w("def deltaChi : ℚ := %s" % qlean(deltaChi))
w("def totalOK : Bool :=")
w("  decide ((∑ n ∈ range NH, errHq n) + (∑ l ∈ range Jd, (NH : ℚ) * eDQ * (2 ^ (2 * l + 1) + 1)) + tauQ ≤ dQtot) &&")
w("  decide ((∑ n ∈ range NH, errEq n) + eEQ + tauE ≤ deltaE) && decide (0 < EQ - deltaE) &&")
w("  decide ((dQtot + deltaP) / (2 * (EQ - deltaE)) + Pmax * deltaE / (2 * (EQ - deltaE) * EQ) ≤ deltaChi)")
w("")
w("/-- The certified polynomial for χ: `χ(v) ≈ Σ_{i<NP} chiCo i |v|^i` on `|v| ≤ log 2`. -/")
w("def chiCo (i : ℕ) : ℚ := pco i / (2 * EQ)")
w("")
w("end ArchS10.Data")
open(sys.argv[1], "w").write("\n".join(out) + "\n")
