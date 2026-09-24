"""Pole-free S-local forms: restrict Q_S to {A(g)=0} (for even/odd g this is ghat(+-i/2)=0), i.e.
Connes-Consani's object for S = {} (pure archimedean W_inf on pole-free tests)."""
import sys, json
import mpmath as mp
import wpw, semilocal as sl

def pole_vector(x, N, sector):
    L = mp.log(mp.mpf(x)); om = 2 * mp.pi / L
    idx = list(range(0, N + 1)) if sector == 'even' else list(range(1, N + 1))
    a = {k: (1 / mp.sqrt(L) if k == 0 else mp.sqrt(2 / L)) for k in idx}
    if sector == 'even':
        return [a[j] * (-1) ** j * mp.sinh(L / 4) / ((j * om) ** 2 + mp.mpf(1) / 4) for j in idx]
    return [a[j] * (-1) ** j * (j * om) * mp.sinh(L / 4) / ((j * om) ** 2 + mp.mpf(1) / 4) for j in idx]

def restricted_min(Q, v):
    # orthonormal basis of v-perp via Householder-free Gram-Schmidt on the standard basis
    n = Q.rows
    vv = mp.matrix(v); nv = mp.sqrt(sum(t * t for t in v)); u = [t / nv for t in v]
    # build projector P = I - u u^T, then compress: eigenvalues of P Q P restricted (one extra zero eigenvalue)
    P = mp.eye(n)
    for i in range(n):
        for j in range(n):
            P[i, j] -= u[i] * u[j]
    M = P * Q * P
    E = sorted(mp.eigsy(M, eigvals_only=True))
    # remove the eigenvalue belonging to direction u (it is 0): drop the entry closest to 0 only if ambiguous -- return all
    return E

P = int(sys.argv[1]); N = 28; dps = 50
xs = [float(t) for t in sys.argv[2].split(',')]
for x in xs:
    for sector in ('even', 'odd'):
        Q, L = sl.build_form(x, N, sector, ('slocal', P), dps=dps)
        v = pole_vector(x, N, sector)
        E = restricted_min(Q, v)
        # the projected matrix has an exact zero eigenvalue along u; report the two smallest and the smallest negative
        neg = [e for e in E if e < -mp.mpf(10) ** (-30)]
        print(json.dumps(dict(P=P, x=x, sector=sector, smallest=[mp.nstr(e, 5) for e in E[:3]], min_negative=(mp.nstr(neg[0], 5) if neg else None))), flush=True)
