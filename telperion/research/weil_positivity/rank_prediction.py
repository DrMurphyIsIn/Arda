#!/usr/bin/env python3
"""Compare the number of Gram eigenvalues above 1e-8 with a zero-count prediction.

Under RH (true for the zeros used here) G = sum_{gamma>0} 2 Re(v_gamma v_gamma^*), v_gamma,j = F_j(1/2 + i gamma).
Each zero contributes a rank-2 piece (cos and sin parts) of generalized size w(gamma) = v^* M^{-1} v.
Prediction: count ~ min(n, 2 * #{gamma : w(gamma) > 1e-8}).  float64 heuristic only.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import json, glob, math
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
Z = np.array([float(x) for x in json.load(open(os.path.join(os.path.dirname(HERE), "zeros2000.json")))])
M8 = lambda m: [0.0, 0.0, 0.0, 0.0][0]


def bspline8_int(m):
    # M8 at integers 0..3 (centered order-8 B-spline)
    vals = {0: 151 / 315, 1: 397 / 1680, 2: 1 / 42, 3: 1 / 5040}
    return vals.get(abs(m), 0.0)


rows = ["basis,a,n,count_gt_1e-8_observed,zeros_with_weight_gt_1e-8,prediction_min(n,2*that)"]
spl = {}
for line in open(os.path.join(RES, "exp1_spline_spectra.csv")).read().splitlines()[1:]:
    f = line.split(",")
    spl[(float(f[0]), int(f[1]))] = int(f[9])
for (a, n), obs in sorted(spl.items()):
    h = 2 * a / (n + 3)
    c = -a + (np.arange(n) + 2) * h
    Mm = np.array([[h * bspline8_int(i - j) for j in range(n)] for i in range(n)])
    Mi = np.linalg.inv(Mm)
    V = h * np.exp(1j * np.outer(c, Z)) * np.sinc(Z * h / 2 / np.pi) ** 4  # n x zeros
    w = np.real(np.einsum("iz,ij,jz->z", V.conj(), Mi, V))
    k = int((w > 1e-8).sum())
    rows.append("spline,%g,%d,%d,%d,%d" % (a, n, obs, k, min(n, 2 * k)))
for f in sorted(glob.glob(os.path.join(RES, "exp12_hermite_*.json"))):
    r = json.load(open(f))
    a, n, sig = float(r["a"]), int(r["n"]), float(r["sigma"])
    u = sig * Z
    P = np.zeros((n, len(Z)))
    P[0] = np.pi ** -0.25 * np.exp(-u * u / 2)
    if n > 1:
        P[1] = math.sqrt(2) * u * P[0]
    for j in range(1, n - 1):
        P[j + 1] = math.sqrt(2 / (j + 1)) * u * P[j] - math.sqrt(j / (j + 1)) * P[j - 1]
    w = 2 * math.pi * sig * (P ** 2).sum(0)
    k = int((w > 1e-8).sum())
    rows.append("hermite,%g,%d,%d,%d,%d" % (a, n, r["count_gt_1e8"], k, min(n, 2 * k)))
open(os.path.join(RES, "exp1_rank_vs_zero_count.csv"), "w").write("\n".join(rows) + "\n")
print("\n".join(rows))
