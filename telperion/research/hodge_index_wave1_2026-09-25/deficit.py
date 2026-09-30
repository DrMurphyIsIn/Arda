from amp import *
for kind in ['zeta', 'E']:
  for (x, kmax, frac, g0) in [(2., 19, 0.3, 14.968), (5., 8, 0.3, 16.568)]:
    te = Test(x, frac, 2, g0)
    t = np.linspace(-4000, 4000, 800001); B = np.max(np.abs(te.F(0.5 + 1j * t))) ** 2
    ks = list(range(1, kmax + 1))
    # reuse prime_side internals for abs sum
    du = 2e-3; u0, h = te.h_grid(du); N = int(x ** kmax) + 2; c = coeffs(kind, N)
    ns = np.nonzero(c)[0]; ns = ns[ns >= 2]; lg = np.log(ns.astype(float)); w = c[ns] / np.sqrt(ns)
    P = prime_side(kind, te, ks)
    hk = h.copy(); print(f'{kind} base x={x} B=sup|F|^2={B:.4f}')
    for k in ks:
        if k > 1: hk = fftconv(hk, h) * du
        gk = fftconv(hk, np.conj(hk[::-1])) * du; L = len(gk); ug = (np.arange(L) - (L - 1) / 2) * du
        ab = np.sum(np.abs(w) * (np.abs(np.interp(lg, ug, np.abs(gk))) + np.abs(np.interp(-lg, ug, np.abs(gk)))))
        s = P[k]['s'].real; pr = P[k]['prime']
        if k in (1, 2, 4, 8, 12, 16, 19) or k == kmax:
            print(f'  k={k:2d} s_k={s:+.4e} s_k^(1/k)/B={np.sign(s)*abs(s)**(1/k)/B:+.4f} |prime|={abs(pr):.3e} abs-sum={ab:.3e} arch={P[k]["arch"]:.3e}  deficit=(1/k)log(abs/|s|)={np.log(ab/abs(s))/k:.4f}  (1/2)log x={0.5*np.log(x):.4f}')
