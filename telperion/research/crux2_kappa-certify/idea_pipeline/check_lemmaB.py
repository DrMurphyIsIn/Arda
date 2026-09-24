"""Numerical spot-check of LEMMA B:  (1/pi) int_0^inf h^2 p |F|^2 dt  <=  A' (1/pi) int_0^inf h^2 |F|^2 dt + err ||f||^2
for f = cos(theta u) 1_[-a,a] (real, even), a = 249/256, eps = 0.34, Tk = 471, w = 50 (as in the certified even run)."""
import mpmath as mp
mp.mp.dps = 20
a = mp.mpf(249)/256; Tk = mp.mpf(471); w = mp.mpf(50)
primes = [(2, mp.log(2)), (3, mp.log(3)), (4, mp.log(2)), (5, mp.log(5))]
Ap = mp.mpf('2.75639')
def p(t): return sum(2*lp/mp.sqrt(n)*mp.cos(t*mp.log(n)) for (n, lp) in primes)
def k(t): return (mp.erf((t + Tk)/w) - mp.erf((t - Tk)/w))/2
def h2(t): return (1 - k(t))**2
def F(t, th):
    # int_{-a}^{a} cos(th u) e^{itu} du = sum of two sincs
    def s(x): return 2*mp.sin(a*x)/x if x != 0 else 2*a
    return (s(t + th) + s(t - th))/2
for th in [0, 50, 300, 471, 480, 600, 1000, 1500]:
    th = mp.mpf(th)
    pts = [0, max(th - 200, 1), th, th + 200, Tk - 3*w, Tk, Tk + 3*w, 3000, 20000]
    pts = sorted(set([mp.mpf(x) for x in pts if x >= 0]))
    lhs = mp.quad(lambda t: h2(t)*p(t)*F(t, th)**2, pts + [mp.inf], maxdegree=8)/mp.pi
    rhs = Ap*mp.quad(lambda t: h2(t)*F(t, th)**2, pts + [mp.inf], maxdegree=8)/mp.pi
    nrm = a + mp.sin(2*a*th)/(2*th) if th != 0 else 2*a
    print("theta=%6s  (1/pi)int h^2 p|F|^2 = %+.4e   A'(1/pi)int h^2|F|^2 = %.4e   ratio lhs/(h2-mass) = %+.3f  (A'=2.756, A_L=4.38)" % (
        mp.nstr(th, 5), float(lhs), float(rhs), float(lhs/(rhs/Ap)) if rhs != 0 else 0))
