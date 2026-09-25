"""Zeros of the Davenport-Heilbronn function D(s) = 5^{-s} [zeta(s,1/5) + k zeta(s,2/5) - k zeta(s,3/5) - zeta(s,4/5)],
k = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1).  Completed: Lam(s) = (5/pi)^{s/2} Gamma((s+1)/2) D(s) = Lam(1 - s).
On-line zeros: sign changes of Z(t) = Lam(1/2 + it) (real).  Off-line zeros: Newton from seeds, then the
Backlund count N(T) = (1/pi) arg Lam along the rectangle checks that nothing is missing.
Single process.  Output: dh_zeros.json {online: [...], offline: [[re, im], ...]}.
"""
import mpmath as mp
import json
import sys

mp.mp.dps = 20
KAP = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)


def D(s):
    return mp.power(5, -s) * (mp.zeta(s, mp.mpf(1) / 5) + KAP * mp.zeta(s, mp.mpf(2) / 5)
                               - KAP * mp.zeta(s, mp.mpf(3) / 5) - mp.zeta(s, mp.mpf(4) / 5))


def Lam(s):
    return mp.power(5 / mp.pi, s / 2) * mp.gamma((s + 1) / 2) * D(s)


def Z(t):
    """real-valued on the line: Lam(1/2+it) scaled by |Gamma| removal for range: use theta-rotation."""
    s = mp.mpc(0.5, t)
    # Lam = (5/pi)^{s/2} Gamma((s+1)/2) D(s); write Gamma = |Gamma| e^{i arg}; Z = e^{i theta} D(1/2+it), real
    th = mp.im(mp.loggamma((s + 1) / 2)) + (t / 2) * mp.log(5 / mp.pi)
    return mp.re(mp.expj(th) * D(s))


def online_zeros(T, step=0.05):
    zs = []
    t = mp.mpf(0.5)
    prev = Z(t)
    while t < T:
        t2 = t + step
        cur = Z(t2)
        if prev == 0:
            zs.append(t)
        elif prev * cur < 0:
            zs.append(mp.findroot(Z, (t, t2), solver='anderson'))
        t, prev = t2, cur
    return zs


def count_N(T):
    """N(T) = #zeros with 0 < Im < T via Riemann-von Mangoldt for D: (1/pi)[theta(T)] + 1 + (1/pi) arg D(1/2+iT)
    with arg by continuous variation from sigma = +inf (sigma = 3 suffices: |D - 1| < 1 there? checked numerically)."""
    s = mp.mpc(0.5, T)
    th = mp.im(mp.loggamma((s + 1) / 2)) + (T / 2) * mp.log(5 / mp.pi)
    # arg D along [3 + iT, 1/2 + iT], continuous
    n = 400
    arg = mp.mpf(0)
    prev = D(mp.mpc(3, T))
    arg = mp.arg(prev)
    for i in range(1, n + 1):
        sig = 3 - (mp.mpf(5) / 2) * i / n
        cur = D(mp.mpc(sig, T))
        dphi = mp.arg(cur / prev)
        arg += dphi
        prev = cur
    # theta(0) correction: Lam argument at t=0 is 0 (real positive), zeros counted: N = (theta + arg D)/pi + 1/2?
    return (th + arg) / mp.pi


if __name__ == '__main__':
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    on = online_zeros(T)
    print('on-line zeros found:', len(on))
    seeds = [(0.808517, 85.699348), (0.650830, 114.163343), (0.574356, 166.479306), (0.724258, 176.702461),
             (0.557945, 224.080208), (0.5, 0)]
    off = []
    for (sr, si) in seeds[:-1]:
        if si > T:
            continue
        try:
            r = mp.findroot(D, mp.mpc(sr, si))
            off.append(r)
            print('off-line zero', mp.nstr(r, 15), ' |D|=', mp.nstr(abs(D(r)), 3))
        except Exception as e:
            print('seed', sr, si, 'failed', e)
    for Tc in [50, 100, 150, 200, 250, 300]:
        if Tc > T:
            continue
        # avoid being at a zero
        Tt = Tc + 0.123
        Nest = count_N(Tt)
        non = sum(1 for z in on if z < Tt)
        noff = sum(2 for z in off if mp.im(z) < Tt)
        print('T=%.3f  N_count(arg)=%s  online=%d  offline(both reflections)=%d  total=%d' % (Tt, mp.nstr(Nest, 6), non, noff, non + noff))
    json.dump({'online': [mp.nstr(z, 18) for z in on], 'offline': [[mp.nstr(mp.re(z), 18), mp.nstr(mp.im(z), 18)] for z in off]},
              open('dh_zeros.json', 'w'))
