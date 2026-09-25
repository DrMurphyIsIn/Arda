from amp import *
cases = [(19., 0.3, 2, 15.668 - 0.7, 3), (12., 0.3, 2, 15.668 - 0.7, 4), (8., 0.45, 2, 15.668 - 1.0, 5), (5., 0.3, 2, 15.668 + 0.9, 8)]
Z = {k: load_zeros(k) for k in ['zeta', 'ZK', 'E']}
for (x, frac, m, g0, kk) in cases:
    te = Test(x, frac, m, g0); ks = list(range(1, kk + 1))
    print(f'--- base x={x}, test (frac={frac}, m={m}, g0={g0:.3f}); windows x^k up to {x**kk:.3g}')
    for kind in ['zeta', 'ZK', 'E']:
        P = prime_side(kind, te, ks)
        zs, lam = zero_side(te, Z[kind], ks)
        row = ' '.join(f'{P[k]["s"].real:+.4e}' for k in ks)
        print(f'  {kind:4s} arith s_k: {row}')
        print(f'  {kind:4s} zeros s_k: ' + ' '.join(f'{zs[k].real:+.4e}' for k in ks))
    # absolute-value (trivial) bound on prime sum vs |s_k| for zeta: cancellation exponent
