"""Exact permanent of a tree's Laplacian, two independent ways (honesty cross-check).

For a tree T, per(L(T)) has a clean combinatorial form: a permutation sigma with
prod_i L[i,sigma(i)] != 0 needs sigma(i) in {i} union N(i); the non-fixed points form
cycles using tree edges, but a tree has no cycle of length >= 3, so cycles are exactly
2-cycles along edges -- i.e. MATCHINGS. Each matched edge contributes (-1)(-1)=1, each
unmatched vertex contributes its diagonal d(v). Hence

    per(L(T)) = sum over matchings M of  prod_{v unmatched by M} d(v).

`tree_laplacian_permanent` evaluates this via an O(n) matching-sum tree DP (exact int).
`ryser_laplacian_permanent` is an independent Ryser evaluation on the full Laplacian
(exact for small n) -- the two must agree (tests enforce it on random trees).
"""
from __future__ import annotations

from fractions import Fraction

import numpy as np


def ryser_laplacian_permanent(M) -> float:
    """Permanent of M via Ryser's formula. Exact-valued for integer M at small n."""
    M = np.asarray(M, dtype=float)
    n = M.shape[0]
    total = 0.0
    for k in range(1 << n):
        cols = [j for j in range(n) if (k >> j) & 1]
        prod = 1.0
        for i in range(n):
            prod *= sum(M[i, j] for j in cols)
        total += ((-1) ** len(cols)) * prod
    return ((-1) ** n) * total


def tree_laplacian_permanent(A) -> int:
    """per(L(T)) via the matching-sum DP: sum_M prod_{unmatched v} deg(v). Exact int."""
    A = np.asarray(A, dtype=int)
    n = A.shape[0]
    if n == 1:
        return 0
    deg = [int(A[i].sum()) for i in range(n)]
    adj = [np.nonzero(A[i])[0].tolist() for i in range(n)]

    # iterative DFS from root 0 to get a parent + visitation order (tree => acyclic)
    root = 0
    parent = [-1] * n
    visited = [False] * n
    order = []
    stack = [root]
    visited[root] = True
    while stack:
        u = stack.pop()
        order.append(u)
        for w in adj[u]:
            if not visited[w]:
                visited[w] = True
                parent[w] = u
                stack.append(w)

    # A_dp[v]: matchings of subtree(v) with v UNMATCHED (v earns weight deg[v]).
    # B_dp[v]: matchings of subtree(v) with v MATCHED to one of its children.
    A_dp = [0] * n
    B_dp = [0] * n
    for u in reversed(order):
        children = [w for w in adj[u] if parent[w] == u]
        tots = [A_dp[c] + B_dp[c] for c in children]
        c_free = 1                      # "u free, weight deferred" = prod of child totals
        for t in tots:
            c_free *= t
        A_dp[u] = deg[u] * c_free
        b = 0
        k = len(children)
        if k:
            pre = [1] * (k + 1)
            for i in range(k):
                pre[i + 1] = pre[i] * tots[i]
            suf = [1] * (k + 1)
            for i in range(k - 1, -1, -1):
                suf[i] = suf[i + 1] * tots[i]
            for j, c in enumerate(children):
                child_free = A_dp[c] // deg[c]   # c free without its own weight
                b += child_free * pre[j] * suf[j + 1]
        B_dp[u] = b
    return A_dp[root] + B_dp[root]


def degree_product(A) -> int:
    A = np.asarray(A, dtype=int)
    p = 1
    for i in range(A.shape[0]):
        p *= int(A[i].sum())
    return p


def laplacian_ratio(A) -> Fraction:
    """pi(T) = per(L(T)) / prod_v deg(v), as an exact Fraction."""
    return Fraction(tree_laplacian_permanent(A), degree_product(A))


def laplacian_ratio_float(A) -> float:
    """Fast float pi(T) = sum_M prod_{uv in M} 1/(d_u d_v) via a matching-sum DP.

    Same value as float(laplacian_ratio(A)) but avoids big-integer permanents --
    for the GA fitness hot path. The exact Fraction path is used by the verifier.
    """
    A = np.asarray(A, dtype=int)
    n = A.shape[0]
    if n <= 1:
        return 0.0
    deg = A.sum(1).astype(float)
    adj = [np.nonzero(A[i])[0].tolist() for i in range(n)]
    parent = [-1] * n
    visited = [False] * n
    order = []
    stack = [0]
    visited[0] = True
    while stack:
        u = stack.pop()
        order.append(u)
        for w in adj[u]:
            if not visited[w]:
                visited[w] = True
                parent[w] = u
                stack.append(w)
    free = [1.0] * n      # v not matched to a child
    matched = [0.0] * n   # v matched to a child
    for u in reversed(order):
        children = [w for w in adj[u] if parent[w] == u]
        tots = [free[c] + matched[c] for c in children]
        fr = 1.0
        for t in tots:
            fr *= t
        free[u] = fr
        k = len(children)
        if k:
            pre = [1.0] * (k + 1)
            for i in range(k):
                pre[i + 1] = pre[i] * tots[i]
            suf = [1.0] * (k + 1)
            for i in range(k - 1, -1, -1):
                suf[i] = suf[i + 1] * tots[i]
            m = 0.0
            for j, c in enumerate(children):
                m += (1.0 / (deg[u] * deg[c])) * free[c] * pre[j] * suf[j + 1]
            matched[u] = m
    return free[0] + matched[0]
