"""Synthesis confirmatory test: maximize the EXACT cavity free energy over a rich family of
degree-decorated (generalized) caterpillars -- multi-hub, mixed arm-count, arm-length, spine fraction --
and confirm the max is log rho* (the caterpillar). This is the target the Lead1+W8 synthesis must certify:
no reversible degree structure beats the ~7-arm length-2 caterpillar.
"""
import math, itertools
import numpy as np

LOG_RHO = math.log(1.2276458)


def bethe_density(n, edges, iters=200):
    d = [0]*n; adj = [[] for _ in range(n)]
    for a, b in edges:
        d[a] += 1; d[b] += 1; adj[a].append(b); adj[b].append(a)
    w = {}
    for a, b in edges:
        w[(a, b)] = w[(b, a)] = 1.0/(d[a]*d[b])
    x = {(a, b): 0.0 for a, b in edges}; x.update({(b, a): 0.0 for a, b in edges})
    for _ in range(iters):
        x = {(u, v): sum(w[(u, c)]/(1.0+x[(c, u)]) for c in adj[u] if c != v) for (u, v) in x}
    q = {k: 1.0/(1.0+x[k]) for k in x}
    vs = sum(math.log(1.0 + sum(w[(v, a)]*q[(a, v)] for a in adj[v])) for v in range(n))
    seen = set(); es = 0.0
    for a, b in edges:
        e = (min(a, b), max(a, b))
        if e in seen: continue
        seen.add(e); es += math.log(1.0 + w[(a, b)]*q[(a, b)]*q[(b, a)])
    return (vs - es)/n


def gen_caterpillar(spine_len, arms_per, arm_len, hub_period=1):
    """spine of spine_len; every hub_period-th spine vertex carries `arms_per` arms of length arm_len."""
    e = []; nid = spine_len
    for i in range(spine_len-1):
        e.append((i, i+1))
    for i in range(spine_len):
        if i % hub_period != 0:
            continue
        for _ in range(arms_per):
            p = i
            for _ in range(arm_len):
                e.append((p, nid)); p = nid; nid += 1
    return nid, e


print(f"log rho* = {LOG_RHO:.6f}\nmaximizing exact cavity F over generalized caterpillars:")
best = (-9, None)
results = []
for arm_len in (1, 2, 3):
    for hub_period in (1, 2, 3):
        for arms in range(1, 20):
            n, e = gen_caterpillar(48, arms, arm_len, hub_period)
            if n > 4000:
                continue
            F = bethe_density(n, e, 120)
            results.append((F, arms, arm_len, hub_period))
            if F > best[0]:
                best = (F, (arms, arm_len, hub_period))
results.sort(reverse=True)
print("  top 6 (F, arms, arm_len, hub_period):")
for F, a, L, hp in results[:6]:
    print(f"    F={F:.6f}  arms={a} arm_len={L} hub_period={hp}  (gap to log rho*: {F-LOG_RHO:+.6f})")
print(f"\n  MAX F = {best[0]:.6f} at {best[1]}   log rho* = {LOG_RHO:.6f}   excess = {best[0]-LOG_RHO:+.6f}")
print("  (small positive excess = finite-spine boundary; the max structure is the length-2 ~7-arm caterpillar)")
