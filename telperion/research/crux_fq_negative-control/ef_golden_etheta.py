"""Negative controls 5 and 6.
(5) Golden fake over F_5.  Genus one: P(T) = 1 + 5T + 5T^2 (m = -5, q = 5); XiA(s) = 5^{s-1/2} P(5^{-s})
    = 2cosh((s-1/2)log5) + sqrt5.  Zeros gamma = (2k+1) pi/log5 -+ i log(phi)/log5 (all off the line).
    Its explicit formula is a complex-shifted lattice Poisson identity whose dual weights are
    (-1)^k (phi^k + phi^-k) (Lucas-type, exponentially growing).  Genus two F(5,5): P = 1+5T+20T^2+25T^3+25T^4,
    dual weights 2 cos(2 pi k/3)(phi^k + phi^-k).  Positivity of the FULL formal-curve dual (N_k >= 0) holds.
(6) Imaginary-shift control E_theta = zeta(s+theta) zeta(s-theta): Euler product, Lambda = Lambda(n)(n^th + n^-th) >= 0,
    decaying dual weights for theta < 1/2, self-dual degree-2 FE; zero measure = zeta's shifted by +-i theta."""
import mpmath as mp
from efcommon import *
mp.mp.dps = 30
phi = (1 + mp.sqrt(5)) / 2
L5 = mp.log(5)

def golden():
    XiA = lambda s: 2 * mp.cosh((s - mp.mpf(1) / 2) * L5) + mp.sqrt(5)
    d = mp.log(phi) / L5
    print("golden: Re rho = 1/2 + log(phi)/log5 =", mp.nstr(mp.mpf(1) / 2 + d, 12), "; first height pi/log5 =", mp.nstr(mp.pi / L5, 12))
    ups = []
    for k in range(0, 60):
        t = (2 * k + 1) * mp.pi / L5
        ups += [mp.mpc(mp.mpf(1) / 2 + d, t), mp.mpc(mp.mpf(1) / 2 - d, t)]
    print("  max |XiA| at the claimed zeros:", mp.nstr(max(abs(XiA(z)) for z in ups), 3))
    # power sums of the inverse roots of 1 + 5T + 5T^2
    q = [mp.mpf(2), mp.mpf(-5)]
    for k in range(2, 40):
        q.append(-5 * q[k - 1] - 5 * q[k - 2])
    for T, w in [(mp.pi / L5 * 7, mp.mpf(1)), (mp.mpf(0), mp.mpf('0.7'))]:
        h, hhat = make_h(T, w)
        Z = zero_sum(h, ups)
        arch = arch_term(h, lambda r: L5, T, w)
        P = mp.mpf(0)
        for k in range(1, 40):
            P += (-q[k] * L5) * mp.power(5, -mp.mpf(k) / 2) * hhat(k * L5)
        P = -P / mp.pi
        print("  Poisson check T=%s w=%s: zero sum %s ; log5-density %s + lattice dual %s ; residual %s"
              % (mp.nstr(T, 8), w, mp.nstr(Z.real, 16), mp.nstr(arch, 12), mp.nstr(P, 12), mp.nstr(Z.real - arch - P, 4)))
    print("  dual weights q_k 5^{-k/2} vs (-1)^k (phi^k+phi^-k):", [(k, mp.nstr(q[k] * mp.power(5, -mp.mpf(k) / 2), 8), mp.nstr((-1) ** k * (phi ** k + phi ** -k), 8)) for k in range(1, 7)])
    N = [5 ** k + 1 - q[k] for k in range(1, 9)]
    print("  genus-one formal-curve counts N_k = 5^k + 1 - q_k (all >= 0 => full dual positive):", [int(mp.nint(x)) for x in N])
    H4 = [1 + 4 ** k - q[k] for k in range(1, 9)]
    print("  H4 = zeta(1+5.5^-s+5.5^-2s)/(1-4.5^-s): Lambda_H4(5^k)/log5 = 1 + 4^k - q_k =", [int(mp.nint(x)) for x in H4],
          "; weights x 5^{-k/2} grow like (4/sqrt5)^k =", mp.nstr(4 / mp.sqrt(5), 6))
    # genus two F(5,5)
    coeffs = [25, 25, 20, 5, 1]   # 25T^4 + 25T^3 + 20T^2 + 5T + 1
    roots = mp.polyroots(coeffs, maxsteps=200, extraprec=60)
    print("  F(5,5): inverse roots alpha = 1/T0:", [mp.nstr(1 / r, 10) for r in roots])
    print("          |alpha|/sqrt5 =", [mp.nstr(abs(1 / r) / mp.sqrt(5), 10) for r in roots], " args/(2pi/3) =", [mp.nstr(mp.arg(1 / r) / (2 * mp.pi / 3), 6) for r in roots])
    pk = lambda k: sum((1 / r) ** k for r in roots)
    print("          dual weights sum alpha^k 5^{-k/2} vs 2cos(2pi k/3)(phi^k+phi^-k):",
          [(k, mp.nstr(mp.re(pk(k)) * mp.power(5, -mp.mpf(k) / 2), 8), mp.nstr(2 * mp.cos(2 * mp.pi * k / 3) * (phi ** k + phi ** -k), 8)) for k in range(1, 7)])
    Nk = [5 ** k + 1 - mp.re(pk(k)) for k in range(1, 7)]
    print("          N_k = 5^k + 1 - sum alpha^k:", [int(mp.nint(x)) for x in Nk], " Weil bound |N_k - 5^k - 1| <= 4 sqrt(5^k)?",
          [bool(abs(Nk[k - 1] - 5 ** k - 1) <= 4 * mp.sqrt(5 ** k)) for k in range(1, 7)])

def etheta(theta=mp.mpf('0.2'), T=mp.mpf(30), w=mp.mpf(1), N=5000):
    zz = []
    n = 1
    while True:
        z = mp.zetazero(n)
        if z.imag > T + 17 * w: break
        if z.imag > T - 17 * w: zz.append(z)
        n += 1
    ups = []
    for z in zz:
        ups += [z + theta, z - theta]
    h, hhat = make_h(T, w)
    A = lambda r: -mp.log(mp.pi) + (mp.re(mp.digamma((mp.mpf(1) / 2 + theta + mp.j * r) / 2)) + mp.re(mp.digamma((mp.mpf(1) / 2 - theta + mp.j * r) / 2))) / 2
    Lam = vonmangoldt_list(N)
    LamT = [Lam[n] * (mp.power(n, theta) + mp.power(n, -theta)) if n >= 2 else 0 for n in range(N + 1)]
    Z = zero_sum(h, ups)
    pole = h(mp.j * (mp.mpf(1) / 2 - theta)) + h(-mp.j * (mp.mpf(1) / 2 - theta)) + h(mp.j * (mp.mpf(1) / 2 + theta)) + h(-mp.j * (mp.mpf(1) / 2 + theta))
    Ar = arch_term(h, A, T, w)
    P = prime_term(LamT, hhat, N)
    print("E_theta theta=%s T=%s w=%s: zero sum (all zeros OFF the line, Re = 1/2 +- theta) %s ; poles(1+-theta)+arch+prime %s ; residual %s"
          % (theta, T, w, mp.nstr(Z.real, 16), mp.nstr((pole + Ar + P).real, 16), mp.nstr((Z - pole - Ar - P).real, 4)))
    print("  Lambda_Etheta(n) >= 0 for all n<=%d: %s ; max Lambda_Etheta(n) n^{-1/2} over n in [N/2,N]: %s (decays like n^{theta-1/2} log n)"
          % (N, all(x >= 0 for x in LamT[2:]), mp.nstr(max(LamT[n] / mp.sqrt(n) for n in range(N // 2, N + 1)), 6)))

golden()
etheta()
etheta(theta=mp.mpf('0.45'), T=mp.mpf(0), w=mp.mpf(3))
