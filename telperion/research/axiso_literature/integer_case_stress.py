"""Stress test of the integer-frequency collapse (scout claim 2) by optimization.

conjecture1_proved = False.  Floating-point evidence only (numpy/scipy SLSQP); not a proof.

Setting.  F(s) = sum f(n) n^{-s} with f periodic mod q, even, real, f(1) = 1 and f >= 0.
F has the zeta-shape functional equation with conductor q and root number +1 exactly when
f is fixed by the unitary DFT mod q (f^ = f; for even f the DFT is the cosine transform).
Our negative control zeta(s)(1 + 4*2^{-s} + 2*4^{-s}) is such an f for q = 4 (f = 7, 1, 5, 1
on residues 0, 1, 2, 3).  The collapse theorem predicts that for q >= 2 no such f has all
log-coefficients c(n) = Lambda_F(n)/log n >= 0.

Test.  For each q, maximize t subject to c(n) >= t for 2 <= n <= N = 3000, f in the (+1)-eigenspace,
f >= 0, f(1) = 1 (SLSQP from random feasible starts, with a cutting-plane working set of
indices n that is enlarged until the working-set optimum is the true minimum over n <= N).  A negative optimum is evidence
for the theorem at that q (the witness n is recorded).  The scout's own check drew random
samples instead of optimizing.
"""
from __future__ import annotations

import cmath
import json
import math
import os

import numpy as np
from scipy.optimize import linprog, minimize
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import spsolve_triangular

HERE = os.path.dirname(os.path.abspath(__file__))
N = 3000
# Dirichlet-convolution matrix pattern on 1..N: row n, column d (d | n), entry a(n/d)
_rows, _cols, _cof = [], [], []
for d in range(1, N + 1):
    for m in range(d, N + 1, d):
        _rows.append(m - 1)
        _cols.append(d - 1)
        _cof.append(m // d)
ROWS, COLS, COF = np.array(_rows), np.array(_cols), np.array(_cof)
LOGS = np.array([0.0] + [math.log(n) for n in range(1, N + 1)])


def selfdual_basis(q: int) -> np.ndarray:
    F = np.array([[cmath.exp(2j * math.pi * r * m / q) for r in range(q)] for m in range(q)]) / math.sqrt(q)
    reps = sorted(set(min(r, (-r) % q) for r in range(q)))
    E = np.zeros((q, len(reps)))
    for j, r in enumerate(reps):
        E[r, j] = 1.0
        E[(-r) % q, j] = 1.0
    M = F @ E - E
    _, s, vh = np.linalg.svd(M)
    null = vh[np.sum(s > 1e-9):].conj().T
    B = (E @ null).real
    # orthonormalize real basis
    u, sv, _ = np.linalg.svd(B, full_matrices=False)
    return u[:, sv > 1e-9]


def log_coeffs(fq: np.ndarray, q: int, nmax: int = N) -> np.ndarray:
    """c(n) = Lambda_F(n)/log n for 2 <= n <= nmax (entries above nmax are 0), from the
    lower-triangular system sum_{d | n} Lambda(d) a(n/d) = a(n) log n (a(1) = 1 on the diagonal)."""
    a = np.array([0.0] + [fq[n % q] for n in range(1, nmax + 1)])
    mask = ROWS < nmax
    A = csr_matrix((a[COF[mask]], (ROWS[mask], COLS[mask])), shape=(nmax, nmax))
    lam = spsolve_triangular(A, a[1:] * LOGS[1:nmax + 1], lower=True)
    c = np.zeros(N + 1)
    c[2:nmax + 1] = lam[1:] / LOGS[2:nmax + 1]
    return c


def run_q(q: int, starts: int, rng) -> dict:
    """Maximize t = min_{2<=n<=N} c(n) over admissible f by SLSQP on a working set W of
    indices (cutting planes): after each solve the full c(2..N) is recomputed and the most
    violated indices are added to W, until the working-set optimum is the true minimum."""
    B = selfdual_basis(q)
    d = B.shape[1]
    A_ub = -B
    b_ub = np.zeros(q)
    A_eq = B[1:2, :]
    b_eq = np.array([1.0])
    feas = linprog(np.zeros(d), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=[(None, None)] * d)
    if not feas.success:
        return {"q": q, "dim_plus_eigenspace": d, "feasible": False}
    best = None
    for _ in range(starts):
        obj = rng.standard_normal(d)
        lp = linprog(obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=[(-50, 50)] * d)
        x = lp.x if lp.success else feas.x
        mix = rng.uniform(0, 1)
        x = mix * x + (1 - mix) * feas.x
        W = list(range(2, 201))
        for _round in range(12):
            nw = max(W)
            idx = np.array(W)
            z0 = np.concatenate([x, [log_coeffs(B @ x, q, nw)[idx].min()]])
            cons = [
                {"type": "ineq", "fun": lambda z: B @ z[:-1]},
                {"type": "eq", "fun": lambda z: (B @ z[:-1])[1] - 1.0},
                {"type": "ineq", "fun": lambda z, idx=idx, nw=nw: log_coeffs(B @ z[:-1], q, nw)[idx] - z[-1]},
            ]
            res = minimize(lambda z: -z[-1], z0, method="SLSQP", constraints=cons,
                           options={"maxiter": 300, "ftol": 1e-12})
            x = res.x[:-1]
            t_w = res.x[-1]
            cfull = log_coeffs(B @ x, q, N)
            worst = np.argsort(cfull[2:])[:10] + 2
            if cfull[2:].min() >= t_w - 1e-9:
                break
            W = sorted(set(W) | set(int(n) for n in worst))
        fq = B @ x
        if fq.min() < -1e-7 or abs(fq[1] - 1) > 1e-7:
            continue
        cfull = log_coeffs(fq, q, N)
        t = cfull[2:].min()
        neg = np.nonzero(cfull[2:] < -1e-9)[0]
        if best is None or t > best["max_min_c"]:
            best = {"max_min_c": float(t), "argmin_n": int(2 + np.argmin(cfull[2:])),
                    "first_negative_n": int(neg[0] + 2) if len(neg) else None,
                    "working_set_size": len(W),
                    "f_mod_q": [round(float(v), 6) for v in fq]}
    return {"q": q, "dim_plus_eigenspace": d, "feasible": True, "starts": starts, "N": N, **(best or {})}


def main() -> None:
    rng = np.random.default_rng(20260923)
    rows = []
    for q in range(2, 25):
        r = run_q(q, starts=6, rng=rng)
        rows.append(r)
        print(q, r.get("dim_plus_eigenspace"), r.get("feasible"), r.get("max_min_c"),
              r.get("argmin_n"), r.get("first_negative_n"), flush=True)
    out = {"conjecture1_proved": False, "N": N,
           "prediction": "max over admissible f of min_{n<=N} c(n) is < 0 for every q >= 2",
           "rows": rows,
           "all_negative": all(r.get("max_min_c", -1) < 0 for r in rows if r.get("feasible"))}
    with open(os.path.join(HERE, "integer_case_stress.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print("all_negative:", out["all_negative"])


if __name__ == "__main__":
    main()
