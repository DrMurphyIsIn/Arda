"""S12 sign check [N-here, float64/mpmath, NOT certified].  conjecture1_proved = False.

Checks the assembly chain in the island's conventions for sample lifts h (g = h' - h/2):
  archW g  = (1/2pi) int (r^2+1/4)|h^(r)|^2 (psiR r - log pi) dr          (S3 archW, S2 hsq_lift)
  E        = -2 eps' (||h||^2 - B),  B = int int conj h(x) h(y) chi(y-x)    (S8 prop55_lift / prop55_KI)
  SoninTr  = archW + Re E   must be >= 0                                    (S7 cc_thm47)
  S12a (L = 1/4):          -Re E >= 2 eps' (1-0.95921)||h||^2 >= 0, so archW >= SoninTr >= 0
  S12b (L = log2/2, int h = 0): -Re E >= 2 eps' (1-0.9995)||h||^2
  6.11 form: archW >= SoninTr - (8*0.058*eps'/log 2) |g^(0)|^2,  g^(0) = -(1/2) int h.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import sys, numpy as np
from scipy.special import psi
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "s11"))
import chico
co = [float(c) for c in chico.load()]
EPS1 = 22.99647568387053
LOG2 = np.log(2.0)

def chi(v):
    a = np.abs(v); return sum(c * a**i for i, c in enumerate(co))

def bump(L, coeffs, n=1201):
    x = np.linspace(-L, L, n)
    s = x / L
    with np.errstate(divide="ignore", over="ignore"):
        b = np.where(np.abs(s) < 1, np.exp(-1.0 / np.maximum(1e-300, 1 - s**2)), 0.0)
    p = sum(c * s**k for k, c in enumerate(coeffs))
    return x, b * p

def check(L, coeffs, label):
    x, h = bump(L, coeffs)
    dx = x[1] - x[0]
    w = np.full_like(x, dx); w[0] = w[-1] = dx / 2
    hn2 = np.sum(w * np.abs(h)**2)
    X, Y = np.meshgrid(x, x, indexing="ij")
    B = np.real(np.sum(w[:, None] * w[None, :] * np.conj(h)[:, None] * h[None, :] * chi(Y - X)))
    E = -2 * EPS1 * (hn2 - B)
    r = np.linspace(-400, 400, 32001); dr = r[1] - r[0]
    hhat = np.array([np.sum(w * h * np.exp(1j * rr * x)) for rr in r])
    psiR = np.real(psi(0.25 + 0.5j * r))
    archW = np.sum((r**2 + 0.25) * np.abs(hhat)**2 * (psiR - np.log(np.pi))) * dr / (2 * np.pi)
    ih = np.sum(w * h)
    g0 = -0.5 * ih
    sonin = archW + E
    print(f"{label}: L={L:.4f} ||h||^2={hn2:.5g} int h={ih:+.3g} B/||h||^2={B/hn2:.5f} "
          f"archW={archW:.6g} E={E:.6g} SoninTr=archW+E={sonin:.6g}")
    return dict(hn2=hn2, B=B, E=E, archW=archW, sonin=sonin, ih=ih, g0=g0)

rng = np.random.default_rng(1)
ok = True
print("--- S12a, L = 1/4, one condition (no int h = 0) ---")
for t in range(6):
    c = rng.normal(size=5) if t else [1.0]
    d = check(0.25, c, f"a{t}")
    ok &= d["sonin"] > -1e-6 and d["B"] <= 0.95921 * d["hn2"] and d["archW"] >= d["sonin"] - 1e-9
print("--- S12b, L = log2/2, int h = 0 ---")
for t in range(6):
    c = rng.normal(size=6)
    x, h = bump(LOG2 / 2, c)
    # project out the mean direction inside the bump class: subtract multiple of an even bump with nonzero mean
    x, h1 = bump(LOG2 / 2, [1.0])
    a = np.trapezoid(h, x) / np.trapezoid(h1, x)
    c2 = list(c); c2[0] -= a
    d = check(LOG2 / 2, c2, f"b{t}")
    ok &= d["sonin"] > -1e-6 and abs(d["ih"]) < 1e-9 and d["B"] <= 0.9995 * d["hn2"] + 1e-9
print("--- 6.11 form, L = log2/2, one condition ---")
c611 = 8 * 0.058 * EPS1 / LOG2
for t in range(4):
    c = rng.normal(size=5) if t else [1.0]
    d = check(LOG2 / 2, c, f"c{t}")
    lhs = d["archW"]; rhs = d["sonin"] - c611 * abs(d["g0"])**2
    print(f"   archW={lhs:.6g} >= SoninTr - {c611:.4f}|g^(0)|^2 = {rhs:.6g}: {lhs >= rhs}")
    ok &= lhs >= rhs
print("c (6.11) =", c611, " gamma = 2*eps'*0.058 =", 2 * EPS1 * 0.058)
print("ALL OK" if ok else "FAILURE")
