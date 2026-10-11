"""S9 certificate generator: certified even prolates (c = 2 pi) via the Galerkin matrix of the
time-band limiting operator in the even monomial basis.  Emits ArchS9_Data.lean.

Math (see telperion/docs/ARCH_S9_NOTES.md):
  T f(w) = int_0^1 2 cos(2 pi x w) f(x) dx;  K_J(w, x) = sum_{j<J} aC_j (w x)^(2j) (Taylor, remainder proved in Lean);
  the rank-J part acts on moments m_j(f) = int_0^1 x^(2j) f.  Its Galerkin pencil (diag(aR) Hilb) is
  eigen-decomposed here at 400 digits: diag(aR) = B^T Theta B + E with B Hilb B^T = I + O(gamma).
  Rows of B (integers over D = 10^P) are the monomial coefficients of the approximate prolates psi_n.
Every inequality used by the Lean frame is re-checked by the kernel; this script only proposes
constants (rounded in the safe direction).  conjecture1_proved = False.
Usage: python gen_s9.py OUT.lean   (pins *_NUM_THREADS=1)"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import sys, math
from fractions import Fraction as F
import mpmath as mp

J = 40          # Taylor / Galerkin size (even monomials x^0 .. x^78)
P = 80          # B = Bz / 10^P
PA = 100        # aR = Az / 10^PA
PT = 160        # theta = Tz / 10^PT
NC = 12         # certified windows n = 0 .. NC
PIDIG = 45
mp.mp.dps = 400

q = int(mp.floor(mp.pi * 10 ** PIDIG))
piLo, piHi = F(q, 10 ** PIDIG), F(q + 1, 10 ** PIDIG)
fact = [math.factorial(i) for i in range(2 * J + 4)]

def aRat(t, j):           # aC_j at pi = t (rational t)
    return F(2 * (-1) ** j * (2 * t) ** (2 * j), fact[2 * j])

c = 2 * mp.pi
Az = [int(mp.nint(2 * (-1) ** j * c ** (2 * j) / mp.factorial(2 * j) * mp.mpf(10) ** PA)) for j in range(J)]
aR = [F(z, 10 ** PA) for z in Az]

H = mp.matrix(J, J)
for i in range(J):
    for k in range(J):
        H[i, k] = mp.mpf(1) / (2 * i + 2 * k + 1)
Lc = mp.cholesky(H)
S = Lc.T * mp.diag([mp.mpf(z) / mp.mpf(10) ** PA for z in Az]) * Lc
E, Y = mp.eigsy(S)
order = sorted(range(J), key=lambda i: -abs(E[i]))
Cm = (Lc ** -1).T * Y
Bz, Tz = [], []
for i in order:
    col = [Cm[k, i] for k in range(J)]
    sg = 1 if col[0] > 0 else -1                     # psi_n(0) > 0
    Bz.append([int(mp.nint(sg * x * mp.mpf(10) ** P)) for x in col])
    Tz.append(int(mp.nint(E[i] * mp.mpf(10) ** PT)))
D = 10 ** P
B = [[F(z, D) for z in row] for row in Bz]
th = [F(z, 10 ** PT) for z in Tz]

# ---------------------------------------------------------------- exact certificate quantities
def up(x, sig=6):
    """smallest decimal with `sig` significant digits that is >= x (x > 0)."""
    x = F(x)
    if x <= 0:
        return F(0)
    e = math.floor(math.log10(x.numerator) - math.log10(x.denominator)) - sig + 1
    s = F(10) ** e
    k = -((-x) // s)
    return k * s

def down(x, sig=6):
    x = F(x)
    e = math.floor(math.log10(x.numerator) - math.log10(x.denominator)) - sig + 1
    s = F(10) ** e
    return (x // s) * s

Lc = 1
for d in range(2 * J - 1):
    Lc = Lc * (2 * d + 1) // math.gcd(Lc, 2 * d + 1)

# Gram (all pairs, exact)
DDL = D * D * Lc
gam = F(0)
for n in range(J):
    for m in range(n, J):
        g = sum(Bz[n][k] * Bz[m][l] * (Lc // (2 * k + 2 * l + 1)) for k in range(J) for l in range(J))
        gam = max(gam, abs(F(g - (DDL if n == m else 0), DDL)))
gamQ = up(gam, 2)
# E rows
eR = []
for j in range(J):
    row = F(0)
    for k in range(J):
        e = (aR[j] if j == k else 0) - sum(th[n] * B[n][j] * B[n][k] for n in range(J))
        row += abs(e)
    eR.append(up(row, 3) if row > 0 else F(1, 10 ** 200))
def Uw(X, j, der):      # weight X^(2j) or 2j X^(2j-1)
    if not der:
        return F(X) ** (2 * j)
    return F(2 * j) * F(X) ** (2 * j - 1) if j > 0 else F(0)
EE = {(X, der): up(sum(eR[j] * Uw(X, j, der) for j in range(J)), 3) for X, der in [(1, False), (2, False), (2, True)]}
aL = [aRat(piLo, j) for j in range(J)]; aH = [aRat(piHi, j) for j in range(J)]
dA = [max(abs(aL[j] - aR[j]), abs(aH[j] - aR[j])) for j in range(J)]
DA = {(X, der): up(sum(dA[j] * Uw(X, j, der) for j in range(J)), 3) for X, der in [(1, False), (2, False), (2, True)]}
ETA = {(1, False): up(4 * (2 * piHi) ** (2 * J) / fact[2 * J], 3),
       (2, False): up(4 * (4 * piHi) ** (2 * J) / fact[2 * J], 3),
       (2, True): up(8 * piHi * (4 * piHi) ** (2 * J - 1) / fact[2 * J - 1], 3)}
ZETA = {k: up(ETA[k] + DA[k] + EE[k], 3) for k in ETA}
z1, z2, zd2 = ZETA[(1, False)], ZETA[(2, False)], ZETA[(2, True)]
Th1 = up(sum(abs(t) for t in th), 8)
eps = up((gamQ * Th1 + z1) * (1 + gamQ), 3)
Cq = up(gamQ * (Th1 * (1 + gamQ)) ** 2, 2)
print("gamma", float(gamQ), "zeta1", float(z1), "zeta2", float(z2), "zetad2", float(zd2), "eps", float(eps), file=sys.stderr)

Psi = [sum(abs(B[m][k]) * 4 ** k for k in range(J)) for m in range(J)]
Psid = [sum(abs(B[m][k]) * 2 * k * F(2) ** (2 * k - 1) for k in range(1, J)) for m in range(J)]

def Rsum(n, w):
    return sum(th[m] ** 2 * eps ** 2 / (abs(th[n] - th[m]) - w) ** 2 for m in range(J) if m != n)

win = []
for n in range(NC + 1):
    w0 = down(min(abs(th[n] - th[m]) for m in range(J) if m != n) / 4, 3)
    R0 = up(Rsum(n, w0), 3)
    pi0 = down(((abs(th[n]) - w0 - z1) ** 2 - R0 - Cq) / th[n] ** 2, 30)
    w1 = up(F(math.sqrt(float(eps ** 2 / pi0))) * F(1001, 1000), 3)
    assert eps ** 2 <= w1 ** 2 * pi0
    R1 = up(Rsum(n, w1), 3)
    pi1 = down(((abs(th[n]) - w1 - z1) ** 2 - R1 - Cq) / th[n] ** 2, 40)
    w2 = up(F(math.sqrt(float(eps ** 2 / pi1))) * F(1001, 1000), 3)
    assert eps ** 2 <= w2 ** 2 * pi1 and pi1 <= 1
    V = up(abs(th[n]) * (1 - pi1 + gamQ) * Psi[n]
           + sum(abs(th[m]) * (eps / (abs(th[n] - th[m]) - w2)) * Psi[m] for m in range(J) if m != n) + z2, 3)
    Vd = up(abs(th[n]) * (1 - pi1 + gamQ) * Psid[n]
            + sum(abs(th[m]) * (eps / (abs(th[n] - th[m]) - w2)) * Psid[m] for m in range(J) if m != n) + zd2, 3)
    win.append(dict(w0=w0, R0=R0, pi0=pi0, w1=w1, R1=R1, pi1=pi1, w2=w2, V=V, Vd=Vd))
    print(n, "theta %.10e w0 %.2e w2 %.2e 1-pi1 %.2e V %.2e Vd %.2e" % (th[n], w0, w2, 1 - pi1, V, Vd), file=sys.stderr)
thc = up(max(abs(th[m]) for m in range(NC + 1, J)), 4)
d0 = up(thc * F(1001, 1000), 4)
SA = up(sum((th[m] ** 2 * eps ** 2 / win[m]["w0"] ** 2) if m <= NC else th[m] ** 2 * eps ** 2 / (d0 - thc) ** 2
            for m in range(J)), 3)
assert SA + Cq < (d0 - z1) ** 2
print("theta_cut", float(thc), "delta0", float(d0), file=sys.stderr)

# ---------------------------------------------------------------- Lean emission
def q(x):
    x = F(x)
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"
def qlist(name, xs):
    return f"def {name} : List ℚ := [" + ", ".join(q(x) for x in xs) + "]"

out = []
w = out.append
w(f"""/-
  ArchS9_Data -- GENERATED by telperion/research/arch_rung/s9/gen_s9.py (do not edit by hand).
  Exact data of the S9 prolate certificate (c = 2 pi, even sector), archimedean stage S9, 2026-10-11.

    * `tabB` : J = {J} rows; row n = integer monomial coefficients (over 10^{P}) of the approximate
      prolate psi_n(x) = sum_k Bq n k x^(2k)  (eigenvectors of the Galerkin pencil diag(aR) Hilb,
      computed at 400 digits; psi_n(0) > 0);
    * `tabT` : the approximate eigenvalues theta_n (over 10^{PT});  `tabA` : aR_j ≈ aC_j (over 10^{PA});
    * constants (gamma, zeta, eps, windows, values) proposed by the generator, every one re-checked
      by `decide +kernel` in the ArchS9_Cert* modules; their soundness is ArchS9_Prolate.
  No analysis here.  conjecture1_proved = False.  No `sorry`.
-/
import Mathlib

open Finset

namespace ArchS9.Data

set_option maxHeartbeats 0
""")
w(f"def Jd : ℕ := {J}")
w(f"def NCw : ℕ := {NC}")
w(f"def DB : ℕ := 10 ^ {P}")
w(f"def DT : ℕ := 10 ^ {PT}")
w(f"def DA : ℕ := 10 ^ {PA}")
w(f"def Lc : ℕ := {Lc}")
w(f"def piLoQ : ℚ := {q} / 10 ^ {PIDIG}".replace("{q}", str(q)) if False else f"def piLoQ : ℚ := {piLo.numerator} / {piLo.denominator}")
w(f"def piHiQ : ℚ := {piHi.numerator} / {piHi.denominator}")
for n in range(J):
    w(f"def rB{n} : List ℤ := [" + ", ".join(str(z) for z in Bz[n]) + "]")
w("def tabB : List (List ℤ) := [" + ", ".join(f"rB{n}" for n in range(J)) + "]")
w("def tabT : List ℤ := [" + ", ".join(str(z) for z in Tz) + "]")
w("def tabA : List ℤ := [" + ", ".join(str(z) for z in Az) + "]")
w("""
def Bz (n k : ℕ) : ℤ := (tabB.getD n []).getD k 0
def Tz (n : ℕ) : ℤ := tabT.getD n 0
def Az (j : ℕ) : ℤ := tabA.getD j 0
def Bq (n k : ℕ) : ℚ := (Bz n k : ℚ) / (DB : ℚ)
def thq (n : ℕ) : ℚ := (Tz n : ℚ) / (DT : ℚ)
def aRq (j : ℕ) : ℚ := (Az j : ℚ) / (DA : ℚ)

/-! Gram matrix in integers: `gz n m / (DB² Lc) = Σ_k Σ_l Bq n k Bq m l / (2k+2l+1)`. -/
def Wz (d : ℕ) : ℤ := ((Lc / (2 * d + 1) : ℕ) : ℤ)
def lcOK : Bool := (List.range (2 * Jd - 1)).all fun d => decide (Lc % (2 * d + 1) = 0)
def gz (n m : ℕ) : ℤ := ∑ k ∈ range Jd, ∑ l ∈ range Jd, Bz n k * Bz m l * Wz (k + l)
def DDL : ℚ := (DB : ℚ) ^ 2 * (Lc : ℚ)
""")
w(f"def gamQ : ℚ := {q(gamQ)}")
w("""def gramRowOK (n : ℕ) : Bool :=
  (List.range' n (Jd - n)).all fun m =>
    decide (|(gz n m : ℚ) - (if n = m then DDL else 0)| ≤ gamQ * DDL)

/-! Rows of `E = diag(aR) - Bᵀ Θ B` in integers: `Ez j k / (DA DT DB²) = E j k`. -/
def Ez (j k : ℕ) : ℤ :=
  (if j = k then Az j * (DT : ℤ) * (DB : ℤ) ^ 2 else 0) - (DA : ℤ) * ∑ n ∈ range Jd, Tz n * Bz n j * Bz n k
def EDEN : ℚ := (DA : ℚ) * (DT : ℚ) * (DB : ℚ) ^ 2
""")
w(qlist("eRL", eR))
w("""def eRq (j : ℕ) : ℚ := eRL.getD j 0
def eRowOK (j : ℕ) : Bool := decide ((∑ k ∈ range Jd, |(Ez j k : ℚ)|) ≤ eRq j * EDEN)

/-! Kernel Taylor coefficients at the pi endpoints, and their spread. -/
def aEnd (t : ℚ) (j : ℕ) : ℚ := 2 * (-1) ^ j * (2 * t) ^ (2 * j) / ((2 * j).factorial : ℚ)
def dAq (j : ℕ) : ℚ := max (|aEnd piLoQ j - aRq j|) (|aEnd piHiQ j - aRq j|)
def wX (X : ℚ) (j : ℕ) : ℚ := X ^ (2 * j)
def wXd (X : ℚ) (j : ℕ) : ℚ := (2 * j : ℚ) * X ^ (2 * j - 1)
""")
w(f"def eta1Q : ℚ := {q(ETA[(1, False)])}")
w(f"def eta2Q : ℚ := {q(ETA[(2, False)])}")
w(f"def etad2Q : ℚ := {q(ETA[(2, True)])}")
w(f"def dA1Q : ℚ := {q(DA[(1, False)])}")
w(f"def dA2Q : ℚ := {q(DA[(2, False)])}")
w(f"def dAd2Q : ℚ := {q(DA[(2, True)])}")
w(f"def E1Q : ℚ := {q(EE[(1, False)])}")
w(f"def E2Q : ℚ := {q(EE[(2, False)])}")
w(f"def Ed2Q : ℚ := {q(EE[(2, True)])}")
w(f"def zeta1Q : ℚ := {q(z1)}")
w(f"def zeta2Q : ℚ := {q(z2)}")
w(f"def zetad2Q : ℚ := {q(zd2)}")
w(f"def Th1Q : ℚ := {q(Th1)}")
w(f"def epsQ : ℚ := {q(eps)}")
w(f"def CQ : ℚ := {q(Cq)}")
w("""
def constOK : Bool :=
  decide (4 * (2 * piHiQ) ^ (2 * Jd) / ((2 * Jd).factorial : ℚ) ≤ eta1Q) &&
  decide (4 * (4 * piHiQ) ^ (2 * Jd) / ((2 * Jd).factorial : ℚ) ≤ eta2Q) &&
  decide (8 * piHiQ * (4 * piHiQ) ^ (2 * Jd - 1) / ((2 * Jd - 1).factorial : ℚ) ≤ etad2Q) &&
  decide ((∑ j ∈ range Jd, dAq j * wX 1 j) ≤ dA1Q) &&
  decide ((∑ j ∈ range Jd, dAq j * wX 2 j) ≤ dA2Q) &&
  decide ((∑ j ∈ range Jd, dAq j * wXd 2 j) ≤ dAd2Q) &&
  decide ((∑ j ∈ range Jd, eRq j * wX 1 j) ≤ E1Q) &&
  decide ((∑ j ∈ range Jd, eRq j * wX 2 j) ≤ E2Q) &&
  decide ((∑ j ∈ range Jd, eRq j * wXd 2 j) ≤ Ed2Q) &&
  decide (eta1Q + dA1Q + E1Q ≤ zeta1Q) &&
  decide (eta2Q + dA2Q + E2Q ≤ zeta2Q) &&
  decide (etad2Q + dAd2Q + Ed2Q ≤ zetad2Q) &&
  decide ((∑ n ∈ range Jd, |thq n|) ≤ Th1Q) &&
  decide ((gamQ * Th1Q + zeta1Q) * (1 + gamQ) ≤ epsQ) &&
  decide (gamQ * (Th1Q * (1 + gamQ)) ^ 2 ≤ CQ) &&
  decide (0 ≤ gamQ) && decide (gamQ < 1 / 1000) && decide (0 ≤ zeta1Q)

/-! The windows `n = 0 .. NCw`. -/
""")
for key in ["w0", "R0", "pi0", "w1", "R1", "pi1", "w2", "V", "Vd"]:
    w(qlist(f"{key}L", [win[n][key] for n in range(NC + 1)]))
w("""def w0q (n : ℕ) : ℚ := w0L.getD n 0
def R0q (n : ℕ) : ℚ := R0L.getD n 0
def pi0q (n : ℕ) : ℚ := pi0L.getD n 0
def w1q (n : ℕ) : ℚ := w1L.getD n 0
def R1q (n : ℕ) : ℚ := R1L.getD n 0
def pi1q (n : ℕ) : ℚ := pi1L.getD n 0
def w2q (n : ℕ) : ℚ := w2L.getD n 0
def Vq (n : ℕ) : ℚ := VL.getD n 0
def Vdq (n : ℕ) : ℚ := VdL.getD n 0

def PsiQ (m : ℕ) : ℚ := ∑ k ∈ range Jd, |Bq m k| * 4 ^ k
def PsidQ (m : ℕ) : ℚ := ∑ k ∈ range Jd, |Bq m k| * ((2 * k : ℚ) * 2 ^ (2 * k - 1))
def gapOK (n : ℕ) (w : ℚ) : Bool :=
  (List.range Jd).all fun m => decide (m ≠ n → 0 < |thq n - thq m| - w)
def Rsum (n : ℕ) (w : ℚ) : ℚ :=
  ∑ m ∈ (range Jd).erase n, thq m ^ 2 * epsQ ^ 2 / (|thq n - thq m| - w) ^ 2
def roundOK (n : ℕ) (w R π0 w1 : ℚ) : Bool :=
  gapOK n w && decide (Rsum n w ≤ R) && decide (0 < |thq n| - w - zeta1Q) &&
  decide (π0 * thq n ^ 2 ≤ (|thq n| - w - zeta1Q) ^ 2 - R - CQ) && decide (0 < π0) &&
  decide (epsQ ^ 2 ≤ w1 ^ 2 * π0) && decide (0 ≤ w1) && decide (0 ≤ w)
def valSum (n : ℕ) (Ψ : ℕ → ℚ) (ζ : ℚ) : ℚ :=
  |thq n| * (1 - pi1q n + gamQ) * Ψ n
    + ∑ m ∈ (range Jd).erase n, |thq m| * (epsQ / (|thq n - thq m| - w2q n)) * Ψ m + ζ
def windowOK (n : ℕ) : Bool :=
  roundOK n (w0q n) (R0q n) (pi0q n) (w1q n) && roundOK n (w1q n) (R1q n) (pi1q n) (w2q n) &&
  gapOK n (w2q n) && decide (pi1q n ≤ 1) && decide (1 / 2 < pi1q n * (1 - gamQ)) &&
  decide (valSum n PsiQ zeta2Q ≤ Vq n) && decide (valSum n PsidQ zetad2Q ≤ Vdq n)
""")
w(f"def thcQ : ℚ := {q(thc)}")
w(f"def d0Q : ℚ := {q(d0)}")
w(f"def SAQ : ℚ := {q(SA)}")
w("""def locOK : Bool :=
  ((List.range Jd).all fun m => decide (NCw < m → |thq m| ≤ thcQ)) &&
  decide (thcQ < d0Q) && decide (zeta1Q ≤ d0Q) &&
  decide ((∑ m ∈ range Jd, (if m ≤ NCw then thq m ^ 2 * epsQ ^ 2 / w0q m ^ 2
      else thq m ^ 2 * epsQ ^ 2 / (d0Q - thcQ) ^ 2)) ≤ SAQ) &&
  decide (SAQ + CQ < (d0Q - zeta1Q) ^ 2) &&
  ((List.range (NCw + 1)).all fun n => decide (0 < w0q n))

end ArchS9.Data
""")
open(sys.argv[1], "w").write("\n".join(out) + "\n")
print("wrote", sys.argv[1], file=sys.stderr)
