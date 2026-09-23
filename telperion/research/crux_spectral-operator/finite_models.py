"""Finite models of the isotropy mechanism (double precision, numpy).

CIRCLE (Iohvidov--Krein).  T Hermitian Toeplitz n x n, lam a simple eigenvalue with k eigenvalues
below it, p(z) = sum v_j z^j the eigenpolynomial.  Shift invariance B(zu, zv) = B(u, v) of the
Toeplitz form B = T - lam on polynomials of degree <= n-2 makes the Jordan chains p/(z - a) of the
roots a inside the unit disk totally B-isotropic, hence
    #{roots with |a| < 1} <= min(k, n-1-k)   and the same for |a| > 1.
LINE (Hermite--Hankel analogue).  H real Hankel, G positive definite Hankel (moments of a positive
measure on R), lam a simple eigenvalue of the pencil H v = lam G v with k pencil eigenvalues below
it.  B = H - lam G is Hankel, so multiplication by z is B-symmetric on degree <= n-2, and
    #{roots of p with Im a > 0} <= min(k, n-1-k).
Both are instances of the kernel-checked abstract theorems iohvidov_krein_circle /
pontryagin_cvs_line (li_positivity island).  We also print the isotropy residual
|B(R_a, R_b)| for roots a, b on the same side and the hyperbolic pairing |B(R_a, R_{a*})|.
"""
import json
import numpy as np

rng = np.random.default_rng(20260923)


def synth_div(p, a):
    """Coefficients (low -> high) of p(z)/(z - a) for a root a of p (length len(p)-1)."""
    n = len(p) - 1
    q = np.zeros(n, dtype=complex)
    acc = 0
    for j in range(n, 0, -1):
        acc = p[j] + acc * a
        q[j - 1] = acc
    return q


def form(u, A, v):
    return np.conj(u) @ A @ v


def circle_trials(ntrials=4000):
    viol = 0
    tot = 0
    attained = 0
    iso_max = 0.0
    hyp_min = np.inf
    for _ in range(ntrials):
        n = int(rng.integers(4, 13))
        c = rng.normal(size=n) + 1j * rng.normal(size=n)
        c[0] = rng.normal()
        T = np.array([[c[i - j] if i >= j else np.conj(c[j - i]) for j in range(n)] for i in range(n)])
        w, V = np.linalg.eigh(T)
        for k in range(n):
            if (k > 0 and w[k] - w[k - 1] < 1e-6) or (k < n - 1 and w[k + 1] - w[k] < 1e-6):
                continue
            v = V[:, k]
            roots = np.roots(v[::-1])
            inside = [a for a in roots if abs(a) < 1 - 1e-7]
            outside = [a for a in roots if abs(a) > 1 + 1e-7]
            bound = min(k, n - 1 - k)
            tot += 1
            if len(inside) > bound or len(outside) > bound:
                viol += 1
            if len(inside) == bound and bound > 0:
                attained += 1
            A = T - w[k] * np.eye(n)
            Rs = [np.concatenate([synth_div(v, a), [0]]) for a in inside]
            nA = np.linalg.norm(A, 2)
            for i, Ri in enumerate(Rs):
                for Rj in Rs:
                    iso_max = max(iso_max, abs(form(Ri, A, Rj)) / (np.linalg.norm(Ri) * np.linalg.norm(Rj) * nA))
                a = inside[i]
                astar = 1 / np.conj(a)
                j = int(np.argmin([abs(b - astar) for b in roots]))
                if abs(roots[j] - astar) < 1e-6:
                    Rp = np.concatenate([synth_div(v, roots[j]), [0]])
                    hyp_min = min(hyp_min, abs(form(Ri, A, Rp)) / (np.linalg.norm(Ri) * np.linalg.norm(Rp) * nA))
    return dict(model='circle (Hermitian Toeplitz)', eigenpolynomials=tot, violations=viol,
                bound_attained_with_bound_positive=attained,
                max_isotropy_residual=float(iso_max), min_hyperbolic_pairing=float(hyp_min))


def line_trials(ntrials=4000):
    viol = 0
    tot = 0
    attained = 0
    iso_max = 0.0
    for _ in range(ntrials):
        n = int(rng.integers(3, 8))
        # G: moments of a positive discrete measure on [-1, 1] with > n atoms (positive definite)
        m = n + 3
        t = rng.uniform(-1, 1, size=m)
        wts = rng.uniform(0.2, 1.0, size=m)
        mom = np.array([np.sum(wts * t ** r) for r in range(2 * n - 1)])
        G = np.array([[mom[i + j] for j in range(n)] for i in range(n)])
        h = rng.normal(size=2 * n - 1)
        H = np.array([[h[i + j] for j in range(n)] for i in range(n)])
        # pencil H v = lam G v via Cholesky
        Lc = np.linalg.cholesky(G)
        Li = np.linalg.inv(Lc)
        S = Li @ H @ Li.T
        S = (S + S.T) / 2
        lamv, Y = np.linalg.eigh(S)
        for k in range(n):
            if (k > 0 and lamv[k] - lamv[k - 1] < 1e-6) or (k < n - 1 and lamv[k + 1] - lamv[k] < 1e-6):
                continue
            v = Li.T @ Y[:, k]
            v = v / np.linalg.norm(v)
            A = H - lamv[k] * G
            if np.linalg.norm(A @ v) > 1e-6 * np.linalg.norm(A, 2):
                continue
            roots = np.roots(v[::-1])
            upper = [a for a in roots if a.imag > 1e-7 * max(1, abs(a))]
            bound = min(k, n - 1 - k)
            tot += 1
            if len(upper) > bound:
                viol += 1
            if len(upper) == bound and bound > 0:
                attained += 1
            Rs = [np.concatenate([synth_div(v.astype(complex), a), [0]]) for a in upper]
            nA = np.linalg.norm(A, 2)
            for Ri in Rs:
                for Rj in Rs:
                    iso_max = max(iso_max, abs(form(Ri, A, Rj)) / (np.linalg.norm(Ri) * np.linalg.norm(Rj) * nA))
    return dict(model='line (Hankel pencil)', eigenpolynomials=tot, violations=viol,
                bound_attained_with_bound_positive=attained, max_isotropy_residual=float(iso_max))


if __name__ == '__main__':
    out = [circle_trials(), line_trials()]
    for r in out:
        print(json.dumps(r))
    json.dump(out, open('finite_models.json', 'w'), indent=1)
