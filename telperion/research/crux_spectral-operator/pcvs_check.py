"""Pontryagin--Caratheodory--Fejer check on Galerkin truncations of the window Weil form.

THEOREM (kernel-checked abstract core in Crux/Crux_spectral_operator.lean, li_positivity island;
the glue to Galerkin matrices is the displacement identity verified in validate_forms.py).
Let c be an eigenvector of the even-sector Galerkin matrix Q_e at a simple eigenvalue lam, and
let F be its transform, F(z) = (2 sin(zL/2)/z) h(z^2).  Then
    (E)  #{roots w of h with Im w > 0} <= kappa_e(lam) := #{even eigenvalues < lam},
i.e. the zeros of F in the open first quadrant number at most kappa_e(lam), and
    (F)  2 #{Im w > 0} + #{w < 0}  <= kappa_e(lam) + kappa_o(lam),
i.e. the zeros of F in the open upper half-plane (first + second quadrant + positive imaginary
axis) number at most the full-space index.  Same for odd eigenvectors with h_o.
The script also checks the mechanism: R = (Omega - w0)^{-1} c is B-isotropic,
B(R, R) = R^* (Q - lam) R = 0, while B(R, conj R) != 0 (a hyperbolic plane).

usage: python3 pcvs_check.py kind x N dps neig
"""
import sys
import json
import time
import mpmath as mp
import wpw


def secular_R(c, L, w0, sector):
    """Coefficient vector of R = F/(z^2 - w0): samples divided by (omega_k^2 - w0)."""
    om2 = wpw.omega2(L, len(c) - 1 if sector == 'even' else len(c), sector)
    return [c[i] / (om2[i] - w0) for i in range(len(c))]


def herm(u, A, v):
    """u^* A v."""
    n = len(u)
    return mp.fsum(mp.conj(u[i]) * mp.fsum(A[i, j] * v[j] for j in range(n)) for i in range(n))


def run(kind, x, N, dps, neig):
    mp.mp.dps = dps
    tol = mp.mpf(10) ** (-(dps // 3))
    t0 = time.time()
    Lam = wpw.von_mangoldt(int(x)) if kind == 'zeta' else wpw.lambda_dh(int(x))
    Qe, L = wpw.build(x, N, kind, 'even', Lam=Lam)
    Qo, _ = wpw.build(x, N, kind, 'odd', Lam=Lam)
    Ee, Ve = mp.eigsy(Qe)
    Eo, Vo = mp.eigsy(Qo)
    ie = sorted(range(len(Ee)), key=lambda i: Ee[i])
    io = sorted(range(len(Eo)), key=lambda i: Eo[i])
    ev_e = [Ee[i] for i in ie]
    ev_o = [Eo[i] for i in io]
    res = dict(kind=kind, x=x, N=N, dps=dps, build_eig_seconds=round(time.time() - t0, 1),
               even_lowest=[mp.nstr(v, 5) for v in ev_e[:neig + 2]],
               odd_lowest=[mp.nstr(v, 5) for v in ev_o[:neig + 2]],
               kappa_even_at_0=sum(1 for v in ev_e if v < 0),
               kappa_odd_at_0=sum(1 for v in ev_o if v < 0), rows=[])
    print(json.dumps({k: v for k, v in res.items() if k != 'rows'}), flush=True)
    for sector, evs, V, order, Q in (('even', ev_e, Ve, ie, Qe), ('odd', ev_o, Vo, io, Qo)):
        M = len(evs)
        for m in range(neig):
            lam = evs[m]
            c = [V[r, order[m]] for r in range(M)]
            ke = sum(1 for v in ev_e if v < lam)
            ko = sum(1 for v in ev_o if v < lam)
            ksec = ke if sector == 'even' else ko
            ws = wpw.w_roots(c, L, sector)
            up, down, neg, pos = wpw.classify_w(ws, tol)
            ok_sector = up <= ksec
            ok_full = 2 * up + neg <= ke + ko
            row = dict(sector=sector, index=m, eig=mp.nstr(lam, 5), kappa_even=ke, kappa_odd=ko,
                       w_upper=up, w_lower=down, w_negative_real=neg, w_positive_real=pos,
                       first_quadrant_zeros=up, upper_halfplane_zeros=2 * up + neg,
                       sector_bound_holds=ok_sector, full_bound_holds=ok_full)
            # the complex zeros themselves (as z = sqrt(w) in the first quadrant)
            zs = [mp.sqrt(w) for w in ws if mp.im(w) > tol * max(1, abs(w))]
            row['first_quadrant_zeros_z'] = [mp.nstr(z, 12) for z in zs]
            # isotropy of R = F/(z^2 - w0) for each upper root w0
            iso = []
            A = Q - lam * mp.eye(M)
            nA = mp.mnorm(A, 1)
            for w in ws:
                if mp.im(w) > tol * max(1, abs(w)):
                    R = secular_R(c, L, w, sector)
                    nR2 = mp.fsum(abs(t) ** 2 for t in R)
                    b_iso = herm(R, A, R) / (nR2 * nA)
                    b_hyp = herm(R, A, [mp.conj(t) for t in R]) / (nR2 * nA)
                    iso.append(dict(w=mp.nstr(w, 10), B_RR_rel=mp.nstr(abs(b_iso), 3),
                                    B_RRbar_rel=mp.nstr(abs(b_hyp), 3)))
            row['isotropy'] = iso
            res['rows'].append(row)
            print(json.dumps(row), flush=True)
    return res


if __name__ == '__main__':
    kind, x, N, dps, neig = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    r = run(kind, x, N, dps, neig)
    json.dump(r, open(f'pcvs_{kind}_x{x}_N{N}.json', 'w'), indent=1)
