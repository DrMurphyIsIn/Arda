"""BUILDER numerical sanity check of Lemma B's two analytic inputs (not a proof; the proof is in NOTES B2):
(1) kcheck(s) = sin(Tk s) e^{-w^2 s^2/4}/(pi s) is the inverse Fourier transform of the erf plateau
    k(t) = (erf((t+Tk)/w) - erf((t-Tk)/w))/2 in the convention F(t) = int f(u) e^{itu} du;
(2) the leakage bound ||(kcheck * f) 1_{|u| > a+eps}|| <= eta ||f||, eta^2 = 4a e^{-w^2 eps^2/2}/(pi^2 eps^3 w^2),
    tested on f = 1_[-a,a] and f = cos(theta u) 1_[-a,a] with moderate parameters where eta is not astronomically small.
conjecture1_proved = False."""
import numpy as np
from scipy.special import erf

def kfun(t, Tk, w):
    return (erf((t + Tk) / w) - erf((t - Tk) / w)) / 2

def kcheck(s, Tk, w):
    s = np.asarray(s, dtype=float)
    out = np.empty_like(s)
    small = np.abs(s) < 1e-12
    out[~small] = np.sin(Tk * s[~small]) * np.exp(-w ** 2 * s[~small] ** 2 / 4) / (np.pi * s[~small])
    out[small] = Tk / np.pi
    return out

Tk, w = 20.0, 8.0
s = np.linspace(-6, 6, 400001)
ds = s[1] - s[0]
ks = kcheck(s, Tk, w)
print("(1) FT of kcheck vs k:")
for t in [0.0, 10.0, 19.0, 20.0, 21.0, 30.0]:
    ft = np.sum(ks * np.cos(t * s)) * ds
    print("   t=%5.1f  int kcheck e^{its} = %.10f   k(t) = %.10f" % (t, ft, kfun(t, Tk, w)))

print("(2) leakage vs eta:")
for (a, eps, w, Tk) in [(1.0, 0.3, 8.0, 20.0), (1.0, 0.4, 10.0, 40.0), (0.97, 0.34, 12.0, 60.0)]:
    eta2 = 4 * a * np.exp(-(w * eps) ** 2 / 2) / (np.pi ** 2 * eps ** 3 * w ** 2)
    v = np.linspace(-a, a, 4001)
    dv = v[1] - v[0]
    wv = np.full_like(v, dv); wv[0] = wv[-1] = dv / 2
    u = np.concatenate([np.linspace(a + eps, a + eps + 4.0, 8001), -np.linspace(a + eps, a + eps + 4.0, 8001)])
    du = 4.0 / 8000
    for theta in [0.0, 5.0, Tk, Tk + 3 * w]:
        fv = np.cos(theta * v)
        nf2 = np.sum(fv ** 2 * wv)
        conv = np.array([np.sum(kcheck(uu - v, Tk, w) * fv * wv) for uu in u])
        leak2 = np.sum(conv ** 2) * du
        print("   a=%.2f eps=%.2f w=%4.1f Tk=%5.1f theta=%5.1f : ||leak||/||f|| = %.3e  <=  eta = %.3e  %s" % (
            a, eps, w, Tk, theta, np.sqrt(leak2 / nf2), np.sqrt(eta2), np.sqrt(leak2 / nf2) <= np.sqrt(eta2)))
