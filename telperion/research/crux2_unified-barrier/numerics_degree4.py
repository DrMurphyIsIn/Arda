"""(a) degree-4 surgery defeating 'P2 at every prime square'; (b) robust-dVP defect constant for W(p,c)."""
import mpmath as mp
mp.mp.dps = 40
# (a) Frobenius roots {i r, -i r, i p/r, -i p/r}: P(T) = (1 + r^2 T^2)(1 + (p/r)^2 T^2)
for p, r2 in [(5, 10), (7, 20), (29, 100)]:
    r = mp.sqrt(r2); roots = [1j*r, -1j*r, 1j*p/r, -1j*p/r]
    t = [sum(x**m for x in roots).real for m in range(0, 9)]
    lam = [1 - t[m] for m in range(1, 9)]          # Lambda_F(p^m)/log p (zeta's 1 included)
    # zeros of local factor in s: p^{-2s} = -1/r^2 or -r^2/p^2  -> Re s = log r / log p or log(p/r)/log p
    re1 = mp.log(r)/mp.log(p); re2 = mp.log(p/r)/mp.log(p)
    print("p=%d r^2=%d: Lambda(p^m)/log p, m=1..8:" % (p, r2), [mp.nstr(v, 6) for v in lam],
          " zero real parts:", mp.nstr(re1, 6), mp.nstr(re2, 6))
    assert lam[0] >= 0 and lam[1] >= 0 and lam[2] >= 0 and lam[3] < 0 and 0.5 < re1 < 1
print("PASS (a): P2 at p, p^2, p^3 holds, fails at p^4; off-line zeros inside the strip")
# (b) robust dVP: negative part of Lambda_W at sigma = 1: B = sum_k max(0, -Lambda_W(p^k)) p^{-k}
def tseq(p, c, M):
    t = [2, -c]
    for m in range(2, M+1): t.append(-c*t[-1] - p*t[-2])
    return t
for (p, c) in [(5, 5), (29, 11), (41, 13), (101, 21), (1009, 64), (29, 29)]:
    t = tseq(p, c, 400)
    B = sum(max(0, -(mp.log(p)*(1 - t[k]))) * mp.power(p, -k) for k in range(1, 401))
    print("(p,c)=(%d,%d): negative-part defect at sigma=1: B = %s" % (p, c, mp.nstr(B, 8)))
print("(c < p+1 => larger Frobenius root < p => B finite; the 3-4-1 argument runs with an additive defect)")
