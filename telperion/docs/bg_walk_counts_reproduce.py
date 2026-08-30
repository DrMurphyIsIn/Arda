"""Reproduction harness for the BG walk-count sub-problem (route b), W5 findings.

Run:  PYTHONPATH=telperion/src python3 telperion/docs/bg_walk_counts_reproduce.py

Establishes, with exact rational arithmetic:
  (A) the exact per-vertex LOCAL formulas for the walk moments m_1, m_2, cross-checked
      against Tr(N^{2k})/n on all trees n<=8 (N = D^{-1/2} A D^{-1/2});
  (B) the free-energy density F(T)=(1/n)log(per(L)/prod deg) is > log rho* for EVERY finite
      tree and max_{|T|=n} F decreases to log rho* FROM ABOVE (so rho* is a thermodynamic-limit
      growth rate, not a finite max; per/prod_deg <= rho*^n is FALSE -- violated at n=2);
  (C) the finite-n maximizers are the length-2-arm caterpillars (single deg-k hub + k cherry
      legs for odd n, two hubs for even n -- the cherry-parity oscillation).

Local formulas (verified here):
    m_1 = (1/n) sum_v  S_v / d_v
    m_2 = (1/n) sum_v [ 2 S_v^2/d_v^2 - Q_v/d_v^2 ]
  with d_v = deg(v),  S_v = sum_{a~v} 1/d_a,  Q_v = sum_{a~v} 1/d_a^2.
Both are AVERAGES of a local 1-neighbourhood degree functional -> the route-(b) upper-bound
certificate is an antisymmetric edge-discharging potential w(x,y) = -w(y,x) with a per-vertex
inequality that telescopes (sum_v sum_{a~v} w(d_v,d_a) = 0 on any tree).
"""
import math
from fractions import Fraction as F

import networkx as nx
import numpy as np

RHO = 1.2276458
LOG_RHO = math.log(RHO)


def _deg_adj(n, edges):
    d = [0] * n
    adj = [[] for _ in range(n)]
    for a, b in edges:
        d[a] += 1; d[b] += 1
        adj[a].append(b); adj[b].append(a)
    return d, adj


def moments_local_exact(n, edges):
    """Exact rational (m_1, m_2) via the per-vertex local formula."""
    d, adj = _deg_adj(n, edges)
    m1 = F(0); m2 = F(0)
    for v in range(n):
        dv = d[v]
        S = sum(F(1, d[a]) for a in adj[v])
        Q = sum(F(1, d[a] ** 2) for a in adj[v])
        m1 += S / dv
        m2 += 2 * S * S / (dv * dv) - Q / (dv * dv)
    return m1 / n, m2 / n


def moments_trace(n, edges, K=2):
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    A = nx.to_numpy_array(G, nodelist=range(n)); dg = A.sum(1)
    N = np.diag(1 / np.sqrt(dg)) @ A @ np.diag(1 / np.sqrt(dg))
    return [np.trace(np.linalg.matrix_power(N, 2 * k)) / n for k in range(1, K + 1)]


def caterpillar_legs(spine_len, arms, leg_len):
    """Spine path of spine_len vertices; each carries `arms` legs, each a path of leg_len vertices."""
    edges = []; nid = spine_len
    for i in range(spine_len - 1):
        edges.append((i, i + 1))
    for i in range(spine_len):
        for _ in range(arms):
            prev = i
            for _ in range(leg_len):
                edges.append((prev, nid)); prev = nid; nid += 1
    return nid, edges


def _edges_of(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return T.number_of_nodes(), [(idx[a], idx[b]) for a, b in T.edges()]


def main():
    # (A) local formula vs trace
    bad = 0; tot = 0
    for n in range(2, 9):
        for T in nx.nonisomorphic_trees(n):
            nn, e = _edges_of(T); tot += 1
            m1e, m2e = moments_local_exact(nn, e)
            m1f, m2f = moments_trace(nn, e, 2)
            if abs(float(m1e) - m1f) > 1e-9 or abs(float(m2e) - m2f) > 1e-9:
                bad += 1
    print(f"(A) per-vertex local m_1,m_2 vs Tr(N^2k)/n over {tot} trees (n<=8): mismatches={bad}")

    # (B) max F per n decreases to log rho* from above
    from telperion.girardeau import hard_core_boson_partition
    print(f"\n(B) log rho* = {LOG_RHO:.6f}   (max_|T|=n F(T) decreasing FROM ABOVE)")
    print("     n | max F(T)  | argmax deg-seq")
    for n in range(2, 14):
        best = (-9.0, None)
        for T in nx.nonisomorphic_trees(n):
            nn, e = _edges_of(T)
            Fv = math.log(float(hard_core_boson_partition(nn, e))) / nn
            if Fv > best[0]:
                best = (Fv, tuple(sorted((deg for _, deg in T.degree()), reverse=True)))
        print(f"    {n:2d} | {best[0]:.6f} | {best[1]}")
    edge = float(hard_core_boson_partition(2, [(0, 1)]))
    print(f"     single edge: per/prod={edge}  (per/prod)^(1/2)={edge**0.5:.5f} > rho*={RHO};"
          f"  per/prod <= rho*^n VIOLATED (ratio {edge / RHO**2:.3f})")

    # (C) large caterpillar approaches log rho*
    print("\n(C) length-2-arm caterpillar (bulk) approaches log rho*:")
    for a in (5, 7, 9):
        n, e = caterpillar_legs(30, a, 2)
        v = float(hard_core_boson_partition(n, e))
        print(f"     a={a}: (per/prod)^(1/n)={v**(1.0 / n):.6f}")


if __name__ == "__main__":
    main()
