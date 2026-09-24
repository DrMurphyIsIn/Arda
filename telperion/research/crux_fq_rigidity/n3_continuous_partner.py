# N3: the continuous Beurling system F(s) = s/(s-1) (dPi = (1-1/x)dx/log x, P_cont = 2 sinh(|u|/2) du)
# has the unique tempered real Guinand partner (zeta archimedean term, unit poles at +-i/2)
#   mu_cont(r) = 1/(pi (1/4 + r^2)) + (1/(2 pi)) (Re psi(1/4 + i r/2) - log pi).
# Check: (a) the GW identity numerically for Gaussian tests; (b) where mu_cont < 0.
import mpmath as mp
mp.mp.dps = 25
Phi = lambda r: mp.re(mp.digamma(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi)
mu = lambda r: 1/(mp.pi*(mp.mpf(1)/4 + r**2)) + Phi(r)/(2*mp.pi)
# (a) GW identity: int ghat dmu  ==  ghat(i/2)+ghat(-i/2) + (1/2pi) int ghat Phi - int g dP_cont
for sig in [0.3, 0.7, 1.5]:
    s = mp.mpf(sig)
    g  = lambda u: mp.e**(-u**2/(2*s**2))
    gh = lambda r: mp.sqrt(2*mp.pi)*s*mp.e**(-s**2*r**2/2)
    lhs = mp.quad(lambda r: gh(r)*mu(r), [-mp.inf, 0, mp.inf])
    pole = 2*mp.sqrt(2*mp.pi)*s*mp.e**(s**2/8)
    arch = mp.quad(lambda r: gh(r)*Phi(r), [-mp.inf, 0, mp.inf])/(2*mp.pi)
    prime = 2*mp.quad(lambda u: g(u)*2*mp.sinh(u/2), [0, mp.inf])
    print(f"sigma={sig}: int ghat dmu_cont = {mp.nstr(lhs,15)}   pole+arch-prime = {mp.nstr(pole+arch-prime,15)}")
# (b) sign of mu_cont
print("mu_cont(0) =", mp.nstr(mu(0),10))
xs = [mp.mpf(k)/20 for k in range(0, 20*40)]
neg = [x for x in xs if mu(x) < 0]
print("mu_cont < 0 on r in [%s, %s] (grid step 0.05, r<=40), count=%d" % (mp.nstr(neg[0],5), mp.nstr(neg[-1],5), len(neg)) if neg else "mu_cont >= 0 on grid")
r0 = mp.findroot(mu, 1.0); r1 = mp.findroot(mu, 6.0)
print("sign changes of mu_cont at r =", mp.nstr(r0,12), "and", mp.nstr(r1,12))
print("min of mu_cont on [0,14]:", mp.nstr(min(mu(x) for x in xs if x<=14),10))
