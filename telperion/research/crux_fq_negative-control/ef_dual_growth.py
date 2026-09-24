"""Growth / sign / support of the dual (prime-side) weights Lambda_F(n) n^{-1/2} for DH and Epstein(x^2+5y^2),
the objects WITHOUT an Euler product.  Question: does 'decaying dual weights' (S4-type) exclude them?"""
import mpmath as mp
from efcommon import log_deriv_coeffs
mp.mp.dps = 20
N = 60000

def report(name, a):
    Lam = log_deriv_coeffs(a, N)
    print(name)
    B = 2
    while B < N:
        blk = range(B, min(2 * B, N + 1))
        m_half = max(abs(Lam[n]) / mp.sqrt(n) for n in blk)
        m_raw = max(abs(Lam[n]) for n in blk)
        nneg = sum(1 for n in blk if Lam[n] < -1e-12)
        npos = sum(1 for n in blk if Lam[n] > 1e-12)
        print("  n in [%6d,%6d): max|Lam| = %-12s max|Lam| n^-1/2 = %-10s  #neg=%5d #pos=%5d" % (B, 2 * B, mp.nstr(m_raw, 6), mp.nstr(m_half, 6), nneg, npos))
        B *= 2
    psi = mp.mpf(0); out = []
    for n in range(2, N + 1):
        psi += Lam[n]
        if n in (100, 1000, 10000, N):
            out.append((n, mp.nstr(psi, 8)))
    print("  psi_F(x) = sum_{n<=x} Lambda_F(n):", out)

kappa = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
chi = [0, 1, kappa, -kappa, -1]
report("DH", [mp.mpf(0)] + [chi[n % 5] for n in range(1, N + 1)])
r = [0] * (N + 1)
M = int(N ** 0.5) + 1
for m in range(-M, M + 1):
    for n in range(-M, M + 1):
        q = m * m + 5 * n * n
        if 0 < q <= N:
            r[q] += 1
report("Epstein x^2+5y^2 (F = E_Q/2)", [mp.mpf(0)] + [mp.mpf(r[n]) / 2 for n in range(1, N + 1)])
