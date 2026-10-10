from sq import *
N = 32
for x in [1.5, 2.0, 2.5, 3.0, 4.0, 5.0]:
    A = mp.log(x) / 2; lp = mangoldt(int(x))
    ps = sorted(set(p for p in lp if p))
    Mh = sum(float(2 * mp.log(p) * p**-0.5 / (1 - p**-0.5)) for p in ps)  # Herglotz/Poisson local sup
    Mt = sum(float(2 * mp.log(lp[n]) / mp.sqrt(n)) for n in range(2, int(x) + 1) if lp[n])  # trivial atom bound
    r = []
    for par in (0, 1):
        fm = Form(A, 'zeta'); G, P = sector_parts(fm, A, N, par)
        r.append((gmin(P['pole'] + P['arch'], G)[0], gmin(P['pole'] + P['arch'] - P['comb'], G)[0]))
    pa = min(a for a, _ in r); q = min(b for _, b in r)
    print('x=%.1f lam(Pole+Arch)=%+.3f  Poisson-local sum=%.3f  trivial-atom sum=%.3f  lam(Q_zeta)=%+.3e  local-cert=%s' % (x, pa, Mh, Mt, q, pa - Mh > 0), flush=True)
