"""Positive control: Guinand-Weil for zeta itself (same pipeline used for the negative controls)."""
import mpmath as mp
from efcommon import *
mp.mp.dps = 30

def run(T, w, N=2000):
    h, hhat = make_h(T, w)
    A = lambda r: -mp.log(mp.pi) / 2 + mp.re(mp.digamma(mp.mpf(1) / 4 + mp.j * r / 2)) / 2
    zs = []
    n = 1
    while True:
        z = mp.zetazero(n)
        if z.imag > T + 16 * w:
            break
        if z.imag > T - 16 * w:
            zs.append(z)
        n += 1
    Z = zero_sum(h, zs)
    pole = h(mp.j / 2) + h(-mp.j / 2)
    Ar = arch_term(h, A, T, w)
    Lam = vonmangoldt_list(N)
    P = prime_term(Lam, hhat, N)
    rhs = pole + Ar + P
    print("zeta  T=%s w=%s  #zeros used=%d" % (T, w, len(zs)))
    print("  zero side      =", mp.nstr(Z, 20))
    print("  pole+arch+prime=", mp.nstr(rhs, 20), " (pole %s, arch %s, prime %s)" % (mp.nstr(pole, 8), mp.nstr(Ar, 12), mp.nstr(P, 12)))
    print("  residual       =", mp.nstr(Z - rhs, 5))
    return Z - rhs

if __name__ == "__main__":
    run(85.6993484854, 1.5)
    run(0, 3.0)
    run(20, 1.0)
