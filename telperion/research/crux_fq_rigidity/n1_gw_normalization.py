# N1: numerical check of the Guinand-Weil normalization used in NOTES.md (Theorem D proof).
# Single process. mpmath only.
import json, mpmath as mp
mp.mp.dps = 30
Z = [mp.mpf(s) for s in json.load(open('/Users/peterwmurphy/arda-crux-fq/telperion/research/zeros2000.json'))]
def vonmangoldt(n):
    # return log p if n = p^k else 0
    m = n; p = None
    for q in range(2, int(n**0.5)+1):
        if m % q == 0:
            p = q; break
    if p is None: return mp.log(n)  # n prime
    while m % p == 0: m //= p
    return mp.log(p) if m == 1 else mp.mpf(0)
def check(sigma):
    s = mp.mpf(sigma)
    g  = lambda u: mp.e**(-u**2/(2*s**2))
    gh = lambda r: mp.sqrt(2*mp.pi)*s*mp.e**(-s**2*r**2/2)
    zero_side = 2*mp.fsum(gh(t) for t in Z)
    pole = 2*mp.sqrt(2*mp.pi)*s*mp.e**(s**2/8)
    Phi = lambda r: mp.re(mp.digamma(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi)
    arch = mp.quad(lambda r: gh(r)*Phi(r), [-mp.inf, 0, mp.inf])/(2*mp.pi)
    N = int(mp.e**(12*s)) + 2   # g(log n) negligible beyond log n ~ 12 sigma
    prime = mp.fsum(vonmangoldt(n)/mp.sqrt(n)*2*g(mp.log(n)) for n in range(2, N))
    rhs = pole + arch - prime
    return zero_side, pole, arch, prime, rhs
for sig in [0.3, 0.5, 0.8]:
    zs, po, ar, pr, rhs = check(sig)
    print(f"sigma={sig}: zero_side={mp.nstr(zs,15)}  pole={mp.nstr(po,12)} arch={mp.nstr(ar,12)} prime={mp.nstr(pr,12)}  pole+arch-prime={mp.nstr(rhs,15)}  diff={mp.nstr(zs-rhs,5)}")
