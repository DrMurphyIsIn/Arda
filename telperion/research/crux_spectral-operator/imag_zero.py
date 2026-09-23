"""The even-sector form of the idea's claim 2 fails on the imaginary axis; the corrected form holds.

Claim 2 of the idea: "the (kappa+1)-th EVEN eigenvector's transform has at most kappa pairs of
non-real zeros", kappa = kappa_even.  At Davenport-Heilbronn x = 40 (Galerkin N = 60) the even
ground state has kappa_even = 0 yet its transform vanishes at a purely imaginary point +-i y0.
The corrected statements (proved abstractly in Lean, see README):
  first-quadrant zeros <= kappa_even(lam),
  upper-half-plane zeros (incl. the positive imaginary axis) <= kappa_even(lam) + kappa_odd(lam),
and here kappa_odd(lam) = 1 (the odd sector has a negative eigenvalue below lam), so the bound
is attained.  We locate y0 as a sign change of F(i y) and verify it with the secular roots.

usage: python3 imag_zero.py kind x N dps
"""
import sys
import json
import mpmath as mp
import wpw

kind, x, N, dps = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
mp.mp.dps = dps
Lam = wpw.von_mangoldt(int(x)) if kind == 'zeta' else wpw.lambda_dh(int(x))
Qe, L = wpw.build(x, N, kind, 'even', Lam=Lam)
Qo, _ = wpw.build(x, N, kind, 'odd', Lam=Lam)
Ee, Ve = mp.eigsy(Qe)
Eo = mp.eigsy(Qo, eigvals_only=True)
ie = sorted(range(len(Ee)), key=lambda i: Ee[i])
out = dict(kind=kind, x=x, N=N, dps=dps, rows=[])
tol = mp.mpf(10) ** (-(dps // 3))
for m in range(3):
    lam = Ee[ie[m]]
    c = [Ve[r, ie[m]] for r in range(N + 1)]
    ws = wpw.w_roots(c, L, 'even')
    negs = [mp.re(w) for w in ws if abs(mp.im(w)) <= tol * max(1, abs(w)) and mp.re(w) < 0]
    ys = [mp.sqrt(-w) for w in negs]
    checks = []
    for y in ys:
        # the transform on the imaginary axis is real; check a sign change around i y
        f = lambda t: mp.re(wpw.transform(c, L, 1j * t, 'even'))
        checks.append(dict(y0=mp.nstr(y, 20), F_at_iy0_rel=mp.nstr(abs(f(y)) / max(abs(f(y * 0.9)), abs(f(y * 1.1))), 3),
                           sign_change=bool(f(y * (1 - mp.mpf(10) ** -8)) * f(y * (1 + mp.mpf(10) ** -8)) < 0)))
    row = dict(index=m, eig=mp.nstr(lam, 6),
               kappa_even=sum(1 for v in Ee if v < lam), kappa_odd=sum(1 for v in Eo if v < lam),
               imaginary_axis_zeros=checks,
               endpoint_value_f_of_L_over_2=mp.nstr(c[0] / mp.sqrt(L) + sum(c[k] * mp.sqrt(2 / L) * (-1) ** k for k in range(1, N + 1)), 5))
    out['rows'].append(row)
    print(json.dumps(row), flush=True)
json.dump(out, open(f'imag_zero_{kind}_x{x}_N{N}.json', 'w'), indent=1)
