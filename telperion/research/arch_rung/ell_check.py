"""CC Cor 2.3(ii): ell(t) = 2 theta'(t) + delta_hat(t) >= 0, with 2 theta'(t) = psiR(t) - log pi (CC (153))
and delta_hat(t) = int_R delta(e^{|u|}) e^{-itu} du = 2 int_0^inf delta(e^u) cos(tu) du (CC: delta(rho^{-1}) = delta(rho)).
delta(e^u) ~ e^{-u/2} as u -> inf, so the integral converges absolutely.  Numerical (mpmath quadosc), NOT certified.
2026-10-11.  conjecture1_proved = False."""
import mpmath as mp
mp.mp.dps = 20


def delta_e(u):
    rho = mp.e ** u
    a, b = 2 * mp.pi * (1 + rho), 2 * mp.pi * (rho - 1)
    tb = mp.si(b) / b if b != 0 else mp.mpf(1)
    return 2 * mp.sqrt(rho) * (mp.si(a) / a + tb)


def dhat(t):
    f = lambda u: delta_e(u) * mp.cos(t * u)
    return 2 * mp.quad(f, [0, 1, 2, 4, 8, 16, 32, 64, mp.inf])


def ell(t):
    return mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * mp.mpf(t) / 2)) - mp.log(mp.pi) + dhat(t)


vals = [(t, float(ell(t))) for t in [0, 0.25, 0.5, 0.75, 1, 1.5, 2, 3, 4, 5, 6, 7, 8, 10, 14, 20]]
for t, v in vals:
    print(f"t = {t:5.2f}: 2theta'(t) = {float(mp.re(mp.digamma(0.25 + 0.5j * t)) - mp.log(mp.pi)):+.5f}, ell(t) = {v:+.6f}")
tmin = mp.findroot(lambda t: mp.diff(ell, t), 0.6) if False else None
print("min over sampled t:", min(v for _, v in vals))
