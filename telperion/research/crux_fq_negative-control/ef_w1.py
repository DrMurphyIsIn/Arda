"""Negative control 2: one-prime surgered zeta W1 = zeta(s) * E(s), E(s) = 1 + 11*29^{-s} + 29*29^{-2s}
(exact FE conductor 841: 29^s E(s) = 29^s + 11 + 29^{1-s}; Euler product; Lambda_W1(29^k) = log29 (1 - p_k),
p_k power sums of the inverse roots of 1 + 11T + 29T^2; exact off-line zeros Re s = 0.5612 / 0.4388 at
Im s = (2m+1) pi/log 29).  Guinand-Weil for W1 = zeta's formula + the conductor term + the E-lattice Poisson
identity, whose dual weights (-1)^k (r^k + r^-k), r = 1.2289, GROW (complex-shifted lattice comb)."""
import mpmath as mp
from efcommon import *
mp.mp.dps = 30
p, c = 29, 11
L = mp.log(p)

def E(s):
    return 1 + c * mp.power(p, -s) + p * mp.power(p, -2 * s)

def power_sums(K):
    S = [mp.mpf(2), mp.mpf(-c)]
    for k in range(2, K + 1):
        S.append(-c * S[k - 1] - p * S[k - 2])
    return S

def E_zeros_upper(tmax):
    out = []
    disc = mp.sqrt(c * c - 4 * p)
    for u in [(-c + disc) / (2 * p), (-c - disc) / (2 * p)]:
        sig = -mp.log(abs(u)) / L
        m = 0
        while True:
            t = (2 * m + 1) * mp.pi / L
            if t > tmax:
                break
            out.append(mp.mpc(sig, t))
            m += 1
    return out

def main(T, w, N=5000):
    h, hhat = make_h(T, w)
    Ez = E_zeros_upper(T + 17 * w)
    print("E-lattice real parts:", sorted(set([mp.nstr(z.real, 12) for z in Ez])), " max|E(z)| =", mp.nstr(max(abs(E(z)) for z in Ez), 3))
    zz = []
    n = 1
    while True:
        z = mp.zetazero(n)
        if z.imag > T + 17 * w:
            break
        if z.imag > T - 17 * w:
            zz.append(z)
        n += 1
    # FE check of the completed function
    xi = lambda s: s * (s - 1) / 2 * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)
    Phi = lambda s: mp.power(p, s) * E(s) * xi(s)
    for s in [mp.mpc(0.3, 2.1), mp.mpc(0.9, 19.0)]:
        print("FE residual at", s, mp.nstr(abs(Phi(s) - Phi(1 - s)) / abs(Phi(s)), 4))
    A = lambda r: L - mp.log(mp.pi) / 2 + mp.re(mp.digamma(mp.mpf(1) / 4 + mp.j * r / 2)) / 2
    Aconductor = lambda r: L   # the E-part's own archimedean (conductor) density
    Lam = vonmangoldt_list(N)
    S = power_sums(40)
    LamW = list(Lam)
    LamE = {}
    k = 1
    while p ** k <= N:
        LamW[p ** k] = Lam[p ** k] + (-S[k]) * L
        LamE[p ** k] = (-S[k]) * L
        k += 1
    Zz = zero_sum(h, zz); ZE = zero_sum(h, Ez)
    pole = h(mp.j / 2) + h(-mp.j / 2)
    Ar = arch_term(h, A, T, w)
    P = prime_term(LamW, hhat, N)
    print("W1  T=%s w=%s  zeta zeros used=%d  E zeros used (upper)=%d" % (mp.nstr(T, 10), w, len(zz), len(Ez)))
    print("  zero side: zeta part %s ; E-lattice part %s (imag %s)" % (mp.nstr(Zz.real, 18), mp.nstr(ZE.real, 18), mp.nstr(ZE.imag, 3)))
    print("  pole+arch+prime = %s  (arch %s, prime %s)" % (mp.nstr((pole + Ar + P).real, 18), mp.nstr(Ar, 14), mp.nstr(P, 14)))
    print("  residual (all zeros) =", mp.nstr((Zz + ZE - pole - Ar - P).real, 5))
    # the E-part alone: complex-shifted lattice Poisson identity with growing signed dual weights
    ArE = arch_term(h, Aconductor, T, w)
    PE = mp.mpf(0)
    for kk in range(1, 40):
        PE += (-S[kk]) * L * mp.power(p, -mp.mpf(kk) / 2) * hhat(kk * L)
    PE = -PE / mp.pi
    print("  E-lattice alone: zero sum %s  vs  conductor %s + lattice dual %s = %s ; residual %s"
          % (mp.nstr(ZE.real, 16), mp.nstr(ArE, 12), mp.nstr(PE, 12), mp.nstr(ArE + PE, 16), mp.nstr(ZE.real - ArE - PE, 4)))
    r = abs(S[1] + mp.sqrt(c * c - 4 * p)) / 2 / mp.sqrt(p)
    print("  dual weights of the E-lattice: -Lambda_E(29^k) 29^{-k/2}/log29 = S_k 29^{-k/2}; r=%s, delta=log r/log29=%s" % (mp.nstr(r, 8), mp.nstr(mp.log(r) / L, 8)))
    for kk in range(1, 9):
        print("    k=%d  S_k 29^{-k/2} = %s   (-1)^k (r^k + r^-k) = %s   Lambda_W1(29^k)/log29 = %s"
              % (kk, mp.nstr(S[kk] * mp.power(p, -mp.mpf(kk) / 2), 10), mp.nstr((-1) ** kk * (r ** kk + r ** -kk), 10), mp.nstr(1 - S[kk], 10)))

if __name__ == "__main__":
    main(mp.mpf(21) * mp.pi / L, mp.mpf(1))
    main(mp.mpf(0), mp.mpf('2.5'))
