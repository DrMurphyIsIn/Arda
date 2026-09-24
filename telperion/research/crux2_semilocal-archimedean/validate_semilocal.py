"""Validate the Galerkin forms against zero sums (explicit formula), for zeta and for the golden
surgery fake (p0, c) = (5, 5), whose zero set is zeros(zeta) u {1/2 +- log(phi)/log 5 + i(2k+1)pi/log 5}."""
import json, time
import mpmath as mp
import semilocal as sl
import wpw

zeros = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'zeros2000.json')))

def zeta_zero_sum(c, L, sector):
    tot = mp.mpf(0)
    for g in zeros:
        g = mp.mpf(g)
        F1 = wpw.transform(c, L, g, sector)
        F2 = wpw.transform(c, L, -g, sector)
        tot += abs(F1) ** 2 + abs(F2) ** 2
    return tot

def fake_zero_sum(c, L, sector, p0, cc, K=4000):
    b1, b2 = sl.surgery_roots(p0, cc)
    # zeros of 2cosh(w log p0) + cc/sqrt(p0), w = s - 1/2
    a = mp.mpf(cc) / mp.sqrt(p0)
    lp = mp.log(p0)
    if a > 2:
        d = mp.acosh(a / 2) / lp        # real part offset delta
        tot = mp.mpf(0)
        for k in range(-K, K):
            t = (2 * k + 1) * mp.pi / lp
            Fm = wpw.transform(c, L, mp.mpc(t, -d), sector)
            Fp = wpw.transform(c, L, mp.mpc(t, d), sector)
            tot += 2 * mp.re(Fm * mp.conj(Fp))
        return tot, d
    raise ValueError

mp.mp.dps = 30
out = []
for (x, N, sector) in [(9, 12, 'even'), (9, 12, 'odd'), (20, 16, 'even')]:
    Q, L = sl.build_form(x, N, sector, ('zeta',), dps=30)
    E, V = sl.eigpairs(Q)
    for idx in (0, 3):
        c = V[idx]
        quad = sum(c[i] * Q[i, j] * c[j] for i in range(len(c)) for j in range(len(c)))
        zs = zeta_zero_sum(c, L, sector)
        out.append(dict(kind='zeta', x=x, N=N, sector=sector, eig_index=idx, quad=mp.nstr(quad, 10), zerosum2000=mp.nstr(zs, 10), rel=mp.nstr((quad - zs) / quad, 3)))
        print(out[-1], flush=True)
    QF, L = sl.build_form(x, N, sector, ('surgery', 5, 5), dps=30)
    for idx in (0, 3):
        c = V[idx]
        quadF = sum(c[i] * QF[i, j] * c[j] for i in range(len(c)) for j in range(len(c)))
        zs = zeta_zero_sum(c, L, sector)
        fs, d = fake_zero_sum(c, L, sector, 5, 5, K=3000)
        out.append(dict(kind='golden', x=x, N=N, sector=sector, eig_index=idx, quad=mp.nstr(quadF, 10), zerosum=mp.nstr(zs + fs, 10), fakepart=mp.nstr(fs, 8), delta=mp.nstr(d, 8), rel=mp.nstr((quadF - zs - fs) / quadF, 3)))
        print(out[-1], flush=True)
json.dump(out, open('validate_semilocal.json', 'w'), indent=1)
