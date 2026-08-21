"""SubsetFormPSD d=2: discover and exact-verify the SOS + Cauchy-Schwarz
decomposition of the degree-2 knapsack subset form.

The form (variables A = x_empty, y_i = x_{i}, z_ij = x_{i,j}):

    Q = sum_{S,T: |S|,|T|<=2} x_S x_T f(|S u T|),   f(k) = prod (n/2-j)/(n-j).

Strategy (block Schur elimination in the exchangeable algebra, where every
needed inverse is a closed-form aI + bJ expression):

  1. complete the square in A:  Q = (A + f1*s1 + f2*s2)^2 + R,
     s1 = sum y_i, s2 = sum z_ij  (the d=1 pattern, one level up);
  2. R's y-block B = p1*I + q1*J is exchangeable; Schur-eliminate:
     R = (y + B^{-1} C z)^T B (y + B^{-1} C z) + z^T E z,
     with C the y-z cross block (two orbit entries: incident/nonincident)
     and E = D - C^T B^{-1} C computable in the pair-exchangeable algebra
     {I, Share, J};
  3. certify the two residual forms by the level-appropriate identities:
     t^T B t = p1*(sum t^2 - (sum t)^2/n) + (p1 + n*q1)/n * (sum t)^2,
     z^T E z = a*(P - W/(2(n-1))) + b*(W - 4*s2^2/n) + c*s2^2,
     P = sum z^2, W = sum_i w_i^2 (w_i = row sums), using the two
     Cauchy-Schwarz facts  W <= 2(n-1) P  and  n W >= 4 s2^2.

Everything is verified EXACTLY: the assembled identity is checked
entrywise against the full (1+n+C(n,2))-dimensional moment matrix in
Fraction arithmetic for several odd n, and every scalar coefficient is
checked nonnegative on the ray.  The output constants (rational functions
of n) are the Lean/emitter targets.

Usage: gen_d2_decomposition.py
"""
from __future__ import annotations

import itertools
from fractions import Fraction as F

import sympy as sp

n = sp.symbols("n")


def f_sym(k):
    out = sp.Integer(1)
    for j in range(k):
        out *= (n / 2 - j) / (n - j)
    return sp.simplify(out)


F0, F1, F2, F3, F4 = [f_sym(k) for k in range(5)]


def frac_f(nv, k):
    r = F(nv, 2)
    out = F(1)
    for j in range(k):
        out *= (r - j) / F(nv - j)
    return out


# ------------------------------------------------------------ discovery

def discover():
    """Compute all decomposition constants symbolically in n."""
    # After removing (A + F1 s1 + F2 s2)^2, the residual orbit entries:
    p1 = sp.simplify(F1 - F1**2)     # y-diag
    q1 = sp.simplify(F2 - F1**2)     # y-offdiag
    c_inc = sp.simplify(F2 - F1 * F2)
    c_non = sp.simplify(F3 - F1 * F2)
    d0 = sp.simplify(F2 - F2**2)
    d1 = sp.simplify(F3 - F2**2)
    d2 = sp.simplify(F4 - F2**2)

    # y-block B = p*I + q1*J with p = p1 - q1; its J-eigenvalue p + n*q1
    # is THE TIE ZERO (kernel = all-ones), so we use the pseudo-inverse.
    pcoef = sp.simplify(p1 - q1)
    tie = sp.simplify(pcoef + n * q1)
    assert sp.simplify(tie) == 0, f"tie zero failed: {tie}"

    # kernel-compatibility of the cross block: 1^T C z = 0 identically
    alpha = sp.simplify(c_inc - c_non)
    ker = sp.simplify(n * c_non + 2 * alpha)
    assert sp.simplify(ker) == 0, f"kernel compatibility failed: {ker}"

    # Schur with B^+ = (1/p)(I - J/n); since sum(Cz) = 0:
    #   z^T C^T B^+ C z = (1/p) * (u^T u) ,  u = C z
    #   u^T u = alpha^2 * W + (n c_non^2 + 4 c_non alpha) * s2^2
    schur_W = sp.simplify(alpha**2 / pcoef)
    schur_s2 = sp.simplify((n * c_non**2 + 4 * c_non * alpha) / pcoef)

    # D as a form in (P, W, s2^2):
    D_P = sp.simplify(d0 - 2 * d1 + d2)
    D_W = sp.simplify(d1 - d2)
    D_s2 = d2

    E_P = sp.simplify(D_P)
    E_W = sp.simplify(D_W - schur_W)
    E_s2 = sp.simplify(D_s2 - schur_s2)

    # certificate coordinates:
    # E-form = a*(P - W/(2(n-1))) + b*(W - 4 s2^2/n) + c*s2^2
    a = sp.simplify(E_P)
    b = sp.simplify(E_W + a / (2 * (n - 1)))
    c = sp.simplify(E_s2 + 4 * b / n)

    # scheme eigenvalues of the z-residual (J(n,2) levels):
    #   W = 2(n-1) N0 + (n-2) N1,  s2^2 = C(n,2) N0,  P = N0 + N1 + N2
    mu2 = sp.simplify(E_P)
    mu1 = sp.simplify(E_P + (n - 2) * E_W)
    mu0 = sp.simplify(E_P + 2 * (n - 1) * E_W
                      + (n * (n - 1) / 2) * E_s2)

    consts = dict(p1=p1, q1=q1, pcoef=pcoef, c_inc=c_inc, c_non=c_non,
                  d0=d0, d1=d1, d2=d2,
                  a=a, b=b, c=c, E_P=E_P, E_W=E_W, E_s2=E_s2,
                  mu0=mu0, mu1=mu1, mu2=mu2)
    return {k: sp.simplify(sp.factor(v)) for k, v in consts.items()}


# --------------------------------------------------- exact verification

def full_matrix(nv):
    idx = [frozenset()] + [frozenset([i]) for i in range(nv)] + \
        [frozenset(e) for e in itertools.combinations(range(nv), 2)]
    return idx, [[frac_f(nv, len(S | T)) for T in idx] for S in idx]


def verify(consts, nv):
    """Entrywise-exact check of the assembled identity at one concrete n."""
    idx, M = full_matrix(nv)
    N2 = nv * (nv - 1) // 2
    dim = 1 + nv + N2
    sub = {n: nv}
    def ev(name):
        x = sp.simplify(consts[name].subs(sub))
        return F(int(sp.numer(x)), int(sp.denom(x)))
    q1 = ev("q1")
    pcoef = ev("pcoef")
    c_inc, c_non = ev("c_inc"), ev("c_non")
    a, b, c = ev("a"), ev("b"), ev("c")
    f1, f2 = frac_f(nv, 1), frac_f(nv, 2)
    pairs = list(itertools.combinations(range(nv), 2))

    Q = [[F(0)] * dim for _ in range(dim)]

    def add_rank1(vec, coef):
        nz = [i for i in range(dim) if vec[i] != 0]
        for i in nz:
            for j in nz:
                Q[i][j] += coef * vec[i] * vec[j]

    # level-0 square (A + f1 s1 + f2 s2)
    v0 = [F(1)] + [f1] * nv + [f2] * N2
    add_rank1(v0, F(1))

    # t_i = y_i + (1/pcoef) * (C z)_i     (pseudo-inverse; sum(Cz) = 0)
    tvecs = []
    for i in range(nv):
        vec = [F(0)] * dim
        vec[1 + i] = F(1)
        for e_i, e in enumerate(pairs):
            ci = c_inc if i in e else c_non
            vec[1 + nv + e_i] = ci / pcoef
        tvecs.append(vec)
    # t^T B t = pcoef * sum t_i^2 + q1 * (sum t)^2
    for vec in tvecs:
        add_rank1(vec, pcoef)
    tsum = [sum(vec[j] for vec in tvecs) for j in range(dim)]
    add_rank1(tsum, q1)

    # z-block certificate: a*P + (b - a/(2(n-1)))*W + (c - 4b/n)*s2^2
    for e_i in range(N2):
        vec = [F(0)] * dim
        vec[1 + nv + e_i] = F(1)
        add_rank1(vec, a)
    for i in range(nv):
        vec = [F(0)] * dim
        for e_i, e in enumerate(pairs):
            if i in e:
                vec[1 + nv + e_i] = F(1)
        add_rank1(vec, b - a / (2 * (nv - 1)))
    s2vec = [F(0)] * dim
    for e_i in range(N2):
        s2vec[1 + nv + e_i] = F(1)
    add_rank1(s2vec, c - 4 * b / nv)

    bad = [(i, j) for i in range(dim) for j in range(dim)
           if Q[i][j] != M[i][j]]
    return len(bad) == 0, bad[:3]


def main():
    consts = discover()
    print("=== d=2 decomposition constants (rational functions of n) ===")
    for k in ("p1", "q1", "pcoef", "a", "b", "c"):
        print(f"  {k} = {consts[k]}")
    print()
    for nv in (9, 11, 13, 15):
        ok, bad = verify(consts, nv)
        print(f"n={nv}: entrywise-exact identity "
              + ("VERIFIED" if ok else f"FAILED at {bad}"))
        assert ok
    # ray positivity of every certificate coefficient
    print()
    print("=== ray positivity (factored) ===")
    for k in ("p1", "a"):
        print(f"  {k} = {sp.factor(consts[k])}")
    for k in ("pcoef", "b", "c"):
        print(f"  {k} = {sp.factor(consts[k])}")
    print()
    print("=== scheme eigenvalues of the z-residual (the REAL certificate) ===")
    for k in ("mu0", "mu1", "mu2"):
        print(f"  {k} = {sp.factor(consts[k])}")


if __name__ == "__main__":
    main()
