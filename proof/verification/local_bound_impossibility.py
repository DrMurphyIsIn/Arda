"""RIGOROUS NO-GO: no per-vertex LOCAL bound can prove (C) -- the tie's local densities are FIXED.

(C) [int g dmu_T <= L] would follow from a per-vertex bound c_v := [g(H^T H)]_vv <= L (since
tr(g(H^T H)) = sum_v c_v = N int g dmu_T).  This module proves that bound is IMPOSSIBLE for ANY certificate.

KEY OBSERVATION.  c_v = [g(H^T H)]_vv = sum_j g(lambda_j^2) |<v | eigvec_j>|^2 = int g dmu_v, where mu_v is
the LOCAL spectral measure at vertex v (the diagonal of the spectral projection).  At the tie N(0,5), the
spectrum is EXACTLY {0, 1/2, 11/12} -- the SAME three points at which every valid certificate satisfies
g = f (forced, from dual_certificate_proof_attempt.py).  Hence every local measure mu_v is supported on
{0,1/2,11/12}, so

    c_v(tie) = int g dmu_v = int f dmu_v     is INDEPENDENT of the certificate g

(only the atom values g(0)=f(0), g(1/2)=f(1/2), g(11/12)=f(11/12) enter).  The three vertex-type densities
are the FIXED numbers  c_root = 0.14786,  c_arm = 0.22724,  c_leaf = 0.19767  (sum with multiplicities =
1*c_root + 5*c_arm + 5*c_leaf = 11 L).  Since  c_arm = 0.22724 > L = 0.20659, NO certificate g has c_v <= L
at the arm.

CONFIRMATION (LP, verify()).  Minimising max_v c_v(tie) over ALL polynomial certificates g (any degree,
g=f at the atoms) gives min = 0.227245 > L, INDEPENDENT of degree (5,7,9,13) -- exactly because c_arm is
fixed.  So the per-vertex local decomposition can never yield tr(g(H^T H)) <= N L.

CONSEQUENCE.  Together with (dual_certificate_proof_attempt.py): the rational-coefficient variant is
impossible, and now the per-vertex LOCAL bound is impossible.  Both natural "make (C) checkable" routes are
rigorously dead; (C) is an irreducibly GLOBAL inequality (the excess density at the arms is real and is
balanced ONLY by the deficit at the root/leaves across the whole tree -- the discharging obstruction, now
shown to be un-removable by any choice of certificate).  Proving (C) needs a global tool (moment-cone SDP
with tree constraints, matching/free-probability, ...) not reducible to a local or rational certificate.
(C) remains a strong CANDIDATE; not a theorem.  conjecture1_proved = False.

Self-verifying (numpy + scipy.linprog).
"""
from __future__ import annotations

import math

import numpy as np

L = math.log(621 / 64) / 11


def _tie_M():
    # tie N(0,5): root(a=6) - 5 arms(a=2) - 5 leaves(a=1)
    def build(C):
        edges = []
        a = []
        cnt = [0]

        def rec(nd):
            me = cnt[0]
            cnt[0] += 1
            a.append(len(nd) + 1)
            for ch in nd:
                r = rec(ch)
                edges.append((me, r))
            return me
        rec(C)
        return a, edges, cnt[0]
    tie = tuple(((),) for _ in range(5))
    a, edges, n = build(tie)
    a = np.array(a, dtype=float)
    Dm = np.diag(1 / np.sqrt(a))
    B = np.zeros((n, n))
    for (i, j) in edges:
        B[i, j] += 1
        B[j, i] -= 1
    H = Dm @ B @ Dm
    return H.T @ H, a, n


def verify() -> dict:
    from scipy.optimize import linprog
    f = lambda x: 0.5 * math.log(1 + x)
    M, a, n = _tie_M()
    root = [i for i in range(n) if a[i] == 6][0]
    arm = [i for i in range(n) if a[i] == 2][0]
    leaf = [i for i in range(n) if a[i] == 1][0]

    # (i) c_v(tie) is fixed: compute via the local spectral measure (independent of g among valid certs)
    w, V = np.linalg.eigh(M)  # eigenvalues (should be {0,1/2,11/12}), eigenvectors
    def c_fixed(v):
        return float(sum(f(w[j]) * V[v, j] ** 2 for j in range(n)))
    c_root, c_arm, c_leaf = c_fixed(root), c_fixed(arm), c_fixed(leaf)

    # (ii) LP: min over degree-D certificates (g=f at atoms) of max(c_root,c_arm,c_leaf)
    mins = {}
    for D in [5, 7, 9, 13]:
        nc = D + 1
        Mp = [np.linalg.matrix_power(M, i) for i in range(nc)]
        cobj = np.zeros(nc + 1)
        cobj[-1] = 1
        Aub, bub = [], []
        for v in [root, arm, leaf]:
            Aub.append([Mp[i][v, v] for i in range(nc)] + [-1.0])
            bub.append(0.0)
        Aeq, beq = [], []
        for x in [0.0, 0.5, 11 / 12]:
            Aeq.append([x ** i for i in range(nc)] + [0.0])
            beq.append(f(x))
        res = linprog(cobj, A_ub=np.array(Aub), b_ub=np.array(bub),
                      A_eq=np.array(Aeq), b_eq=np.array(beq),
                      bounds=[(None, None)] * (nc + 1), method="highs")
        mins[D] = round(float(res.fun), 6)
    return {
        "tie_spectrum": sorted(round(x, 6) for x in set(np.round(w, 6))),
        "c_root_fixed": round(c_root, 6),
        "c_arm_fixed": round(c_arm, 6),
        "c_leaf_fixed": round(c_leaf, 6),
        "c_arm_exceeds_L": c_arm > L,
        "L": round(L, 6),
        "min_max_c_v_by_degree": mins,
        "per_vertex_bound_impossible_any_degree": all(v > L + 1e-7 for v in mins.values()),
        "conjecture1_proved": False,
        "statement": ("RIGOROUS NO-GO: c_v(tie)=int g dmu_v is FIXED (independent of the certificate g) "
                      "because the tie spectrum {0,1/2,11/12} = the atoms where g=f; the arm density "
                      "c_arm=0.22724 > L=0.20659, so NO certificate has c_v<=L (LP min = 0.227245 for any "
                      "degree). The per-vertex LOCAL bound cannot prove (C). With the rational-variant no-go, "
                      "both natural 'checkable' routes are dead; (C) is irreducibly GLOBAL. Not a theorem."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
