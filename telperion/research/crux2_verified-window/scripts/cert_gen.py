# Generate an exact-integer Schur/Collatz-Wielandt certificate for
#     A_win(L'; L') = || sum_{n <= 99 prime power} (Lambda(n)/sqrt n)(tau_{log n} + tau_{log n}^*) ||_{L^2[-L',L']}
# and check it with the SAME integer algorithm the Lean kernel runs (Crux2_verified_window.lean, `check`).
# Usage: python3 cert_gen.py <Lp_num> <Lp_den> <N> <iters> [emit_json]
import math, sys, json
from fractions import Fraction as Fr
import numpy as np
from logbounds import compute as log_compute

def prime_powers(nmax):
    out = []
    for n in range(2, nmax + 1):
        m = n; p = None
        for d in range(2, n + 1):
            if m % d == 0:
                p = d; break
        k = 0
        while m % p == 0:
            m //= p; k += 1
        if m == 1:
            out.append((n, p, k))
    return out

def isqrt_frac_lower(n, den=10 ** 9):
    # rational s <= sqrt(n) with denominator den (exact when n is a perfect square)
    r = math.isqrt(n)
    if r * r == n: return Fr(r)
    s = math.isqrt(n * den * den)  # floor(sqrt(n) * den)
    return Fr(s, den)

class Cert:
    def __init__(self, Lp, N, H=10 ** 7, S=10 ** 9):
        self.Lp = Lp; self.N = N; self.H = H; self.S = S
        self.h = 2 * Lp / N; self.q = self.h / H
        lo, hi, _ = log_compute()
        nmax = 99
        assert math.exp(2 * float(Lp)) < 100.0 or True
        self.pp = [t for t in prime_powers(nmax)]
        ds = []
        for (n, p, k) in self.pp:
            lo_n = k * lo[p]; hi_n = k * hi[p]
            A = math.floor(lo_n / self.q); B = math.ceil(hi_n / self.q)
            assert Fr(A) * self.q <= lo_n and hi_n <= Fr(B) * self.q
            s = isqrt_frac_lower(n)
            assert s * s <= n
            C = math.ceil(Fr(S) * hi[p] / s)
            ds.append(dict(n=n, p=p, k=k, A=A, B=B, C=C, s=s, lo=lo_n, hi=hi_n))
        self.ds = ds

    # ---- the integer checker (mirrors Lean) ----
    def maxR(self, w, lo, hi):
        if hi + 1 <= lo: return 0
        return max(w[lo:hi + 1])
    def mminus(self, w, k, A, B):
        N, H = self.N, self.H
        if (k + 1) * H < A: return 0
        lo = max(k * H - B, 0) // H
        hi = min(((k + 1) * H - A) // H, N - 1)
        return self.maxR(w, lo, hi)
    def mplus(self, w, k, A, B):
        N, H = self.N, self.H
        lo = (k * H + A) // H
        if N < lo: return 0
        return self.maxR(w, min(lo, N - 1), min((k * H + H + B) // H, N - 1))
    def rows(self, w):
        return [sum(d['C'] * (self.mminus(w, k, d['A'], d['B']) + self.mplus(w, k, d['A'], d['B'])) for d in self.ds)
                for k in range(self.N)]
    def lam_of(self, w):
        rs = self.rows(w)
        Lam = max(-(-r // wk) for r, wk in zip(rs, w))  # ceil
        return Lam, rs

def galerkin_vec(Lp, N, pp):
    Lp = float(Lp); h = 2 * Lp / N
    x = -Lp + h * np.arange(N)
    M = np.zeros((N, N))
    for (n, p, k) in pp:
        u = math.log(n)
        if u >= 2 * Lp: continue
        c = math.log(p) / math.sqrt(n)
        D = x[None, :] - x[:, None] - u
        O = np.clip(h - np.abs(D), 0, None) / h
        M += c * (O + O.T)
    ev, vec = np.linalg.eigh(M)
    return ev[-1], np.abs(vec[:, -1])

def optimise(cert, iters, scale=10 ** 9):
    lam_g, v = galerkin_vec(cert.Lp, cert.N, cert.pp)
    w = v / v.max()
    best = None
    for it in range(iters):
        wi = [max(1, int(round(scale * x))) for x in w]
        Lam, rs = cert.lam_of(wi)
        if best is None or Lam < best[0]:
            best = (Lam, wi)
        r = np.array(rs, dtype=float)
        w = 0.5 * w + 0.5 * r / r.max()
        w = w / w.max()
    return lam_g, best

if __name__ == "__main__":
    Lp = Fr(int(sys.argv[1]), int(sys.argv[2])); N = int(sys.argv[3]); iters = int(sys.argv[4])
    out = sys.argv[5] if len(sys.argv) > 5 else None
    cert = Cert(Lp, N)
    lam_g, (Lam, w) = optimise(cert, iters)
    print(f"L'={Lp} N={N} h={cert.h} H={cert.H} S={cert.S} shifts={len(cert.ds)} galerkin_lower={lam_g:.6f} "
          f"certified_upper Lam/S={Lam}/{cert.S} = {Lam / cert.S:.6f}  minw={min(w)} maxw={max(w)}")
    # independent re-check with exact integers
    Lam2, rs = cert.lam_of(w)
    assert Lam2 == Lam and all(r <= Lam * wk for r, wk in zip(rs, w)) and all(x > 0 for x in w)
    if out:
        json.dump(dict(Lp=[Lp.numerator, Lp.denominator], N=N, H=cert.H, S=cert.S, Lam=Lam, w=w,
                       ds=[dict(n=d['n'], p=d['p'], k=d['k'], A=d['A'], B=d['B'], C=d['C'],
                                s=[d['s'].numerator, d['s'].denominator]) for d in cert.ds],
                       galerkin_lower=lam_g), open(out, 'w'))
        print("wrote", out)
