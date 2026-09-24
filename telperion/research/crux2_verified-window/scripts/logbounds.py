# Rigorous rational enclosures of log p (p prime <= 97), computed EXACTLY the way the Lean file proves them:
#   log 2 in (0.6931471803, 0.6931471808)                         [Mathlib Real.log_two_gt_d9 / lt_d9]
#   log p = log m + log(1 - x),  m = smooth neighbour of p,  x = (m - p)/m,
#   |sum_{i<K} x^(i+1)/(i+1) + log(1 - x)| <= |x|^(K+1)/(1 - |x|)   [Mathlib Real.abs_log_sub_add_sum_range_le]
# Final bounds are rounded outward to denominator 10^12 so the Lean statements are short.
from fractions import Fraction as Fr
import math

DEN = 10 ** 12
L2LO = Fr(6931471803, 10 ** 10)
L2HI = Fr(6931471808, 10 ** 10)

PRIMES = [p for p in range(2, 100) if all(p % d for d in range(2, int(p ** 0.5) + 1))]

def factor(m):
    out = {}; d = 2
    while d * d <= m:
        while m % d == 0:
            out[d] = out.get(d, 0) + 1; m //= d
        d += 1
    if m > 1: out[m] = out.get(m, 0) + 1
    return out

def neighbour(p):
    # smooth neighbour m in {p-1, p+1} (both even, factors < p); prefer the one with smaller |x|, i.e. larger m
    return p + 1 if p > 2 else None

def series_terms(x, target=Fr(1, 10 ** 13)):
    ax = abs(x); K = 1
    while ax ** (K + 1) / (1 - ax) > target:
        K += 1
    return K

def compute():
    lo = {2: L2LO}; hi = {2: L2HI}
    rec = {}
    for p in PRIMES[1:]:
        # choose m = p+1 or p-1, whichever has all prime factors < p (both do for p >= 3); take p+1 unless p+1 has factor p (never)
        cands = [p - 1, p + 1]
        best = None
        for m in cands:
            f = factor(m)
            if all(q < p for q in f):
                x = Fr(m - p, m)
                if best is None or abs(x) < abs(best[1]):
                    best = (m, x, f)
        m, x, f = best
        K = series_terms(x)
        S = sum(x ** (i + 1) / (i + 1) for i in range(K))
        E = abs(x) ** (K + 1) / (1 - abs(x))
        # log(1-x) in [-S - E, -S + E]
        l1lo = -S - E; l1hi = -S + E
        lmlo = sum(e * lo[q] for q, e in f.items()); lmhi = sum(e * hi[q] for q, e in f.items())
        plo = lmlo + l1lo; phi = lmhi + l1hi
        # round outward to 1/DEN
        plo_r = Fr(math.floor(plo * DEN), DEN); phi_r = Fr(math.ceil(phi * DEN), DEN)
        lo[p] = plo_r; hi[p] = phi_r
        rec[p] = dict(m=m, x=x, K=K, fac=f, lo=plo_r, hi=phi_r)
    return lo, hi, rec

if __name__ == "__main__":
    lo, hi, rec = compute()
    for p in PRIMES:
        w = float(hi[p] - lo[p])
        print(p, rec.get(p, {}).get('m'), rec.get(p, {}).get('x'), rec.get(p, {}).get('K'), float(lo[p]), math.log(p), float(hi[p]), f"width {w:.2e}",
              lo[p] < Fr(math.log(p)) < hi[p])
