"""D = (1/2)(1-ik)L(chi) + (1/2)(1+ik)L(chibar), chi mod 5, chi(2)=i (odd).
   D = sqrt(1+k^2) sqrt(L Lbar) cos(v - phi), v = Im-part series, phi = arctan k.
   Forms: D exact; D_lin = avg + linear(kappa v) [prime-power supported]; D_quad = + v^2 term."""
from sq import *
kap = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
chi = {0: 0, 1: 1, 2: 1j, 4: -1, 3: -1j}
def chi5(n): return chi[n % 5]
def a_D(n): return mp.re((1 - 1j * kap) * chi5(n))
def cD(nmax):
    a = [mp.mpf(0)] + [a_D(n) for n in range(1, nmax + 1)]
    c = [mp.mpf(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        acc = a[n] * mp.log(n)
        for d in range(2, n):
            if n % d == 0: acc -= c[d] * a[n // d]
        c[n] = acc
    return c
def parts_D(nmax, order):
    lp = mangoldt(nmax)
    avg = [mp.log(lp[n]) * mp.re(chi5(n)) if lp[n] else mp.mpf(0) for n in range(nmax + 1)]
    b = [mp.mpf(0)] * (nmax + 1)  # v = sum b(n) n^-s, u = i v, u = (1/2)log(L/Lbar)
    for n in range(2, nmax + 1):
        if lp[n]:
            k = round(mp.log(n) / mp.log(lp[n])); b[n] = mp.im(chi5(n)) / k
    phi = mp.atan(kap)
    # -d/ds log cos(v - phi) coefficients: log cos(v-phi) = sum_j g_j v^j, g_j = Taylor coeffs at v=0
    g = mp.taylor(lambda t: mp.log(mp.cos(t - phi)), 0, 8)
    acc = [mp.mpf(0)] * (nmax + 1); p = b[:]; j = 1
    while 2 ** j <= nmax and (order is None or j <= order):
        for n in range(nmax + 1): acc[n] += g[j] * p[n]
        p = dconv(p, b, nmax); j += 1
    return avg, [acc[n] * mp.log(n) if n >= 2 else mp.mpf(0) for n in range(nmax + 1)]
def set_fams_D(fm):
    b0, c0 = mp.mpf(3) / 2, mp.log(5 / mp.pi)
    J = int(mp.ceil(80 / fm.a)) + 4; betas = [b0 + 2 * j for j in range(J)]
    CL = c0 + mp.digamma(b0 / 2) + sum(2 * mp.exp(-b * fm.a) / b for b in betas)
    fm.fams = [(b0, betas, CL)]
def formD(A, w):
    fm = Form(A, 'zeta'); set_fams_D(fm)
    fm.pr = [(n, float(w[n] / mp.sqrt(n)), float(mp.log(n))) for n in range(2, fm.nmax + 1) if abs(w[n]) > 1e-30]
    return fm
def lam(A, w, N, withpole=False):
    out = []
    for par in (0, 1):
        G, P = sector_parts(formD(A, w), A, N, par)
        M = P['arch'] - P['comb'] + (P['pole'] if withpole else 0)
        out.append(gmin(M, G)[0])
    return min(out)
if __name__ == '__main__':
    nm = 80; c = cD(nm); avg, cr = parts_D(nm, None)
    print('kappa', mp.nstr(kap, 8), 'c_D(6)', mp.nstr(c[6], 8), '(1+k^2)log6', mp.nstr((1 + kap**2) * mp.log(6), 8))
    print('identity err', mp.nstr(max(abs(c[n] - avg[n] - cr[n]) for n in range(2, nm + 1)), 5))
    N = int(sys.argv[1])
    for x in [float(v) for v in sys.argv[2].split(',')]:
        A = mp.log(x) / 2; n = int(x)
        c = cD(n); avg, cr = parts_D(n, None); _, lin = parts_D(n, 1); _, q2 = parts_D(n, 2)
        w = lambda extra: [avg[i] + extra[i] for i in range(n + 1)]
        print('x=%.1f D=%+.3e avg(GRH)=%+.3e D_lin=%+.3e D_quad=%+.3e' % (x, lam(A, c, N), lam(A, avg, N), lam(A, w(lin), N), lam(A, w(q2), N)), flush=True)
