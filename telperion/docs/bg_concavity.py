"""Lead 3 crux: is the exact cavity free-energy density CONCAVE over structural interpolations?
If concave + the caterpillar is the unique stationary point (a*=7.016), then caterpillar = GLOBAL max = log rho*
(the infinite-tree variational proof), and the Weil-positivity machinery certifies the negative-definite Hessian.

Test: (1) F(a) concavity along the continuous arm-count family; (2) mixed-arm caterpillars (fraction p of
hubs with a1 arms, 1-p with a2, both flanking a*) -- does any mix beat F(a*)?  A concave F has F(mix) <= max.
"""
import math
from scipy.optimize import brentq

LOG_RHO = math.log(1.2276458)


def bethe_density(n, edges, iters=200):
    d = [0]*n; adj = [[] for _ in range(n)]
    for a, b in edges:
        d[a] += 1; d[b] += 1; adj[a].append(b); adj[b].append(a)
    w = {(a, b): 1.0/(d[a]*d[b]) for a, b in edges}
    w.update({(b, a): v for (a, b), v in list(w.items())})
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


def spine_arms(arms_pattern, arm_len=2):
    """spine of len(arms_pattern) hubs; hub i has arms_pattern[i] arms of arm_len."""
    spl = len(arms_pattern); e = []; nid = spl
    for i in range(spl-1):
        e.append((i, i+1))
    for i in range(spl):
        for _ in range(arms_pattern[i]):
            p = i
            for _ in range(arm_len):
                e.append((p, nid)); p = nid; nid += 1
    return nid, e


# (1) F(a) 1-parameter -- but a is integer for real trees; use uniform-a caterpillars, check discrete concavity
print("(1) uniform-a caterpillar F(a) -- discrete second difference (concave if <0):")
Fa = {}
for a in range(3, 12):
    n, e = spine_arms([a]*40, 2)
    Fa[a] = bethe_density(n, e, 120)
for a in range(4, 11):
    d2 = Fa[a+1] - 2*Fa[a] + Fa[a-1]
    print(f"  a={a}: F={Fa[a]:.6f}  F''~{d2:+.6e}  {'concave' if d2 < 0 else 'CONVEX!'}")

# (2) mixed-arm caterpillars: fraction p of hubs have a1, rest a2 (periodic interleave). Concave => no mix beats max.
print("\n(2) mixed-arm (a1=5,a2=9 flanking a*=7): does any mix beat max(F(5),F(9))?  F(7)=%.6f" % Fa[7])
a1, a2 = 5, 9
SP = 60
for num2 in range(0, SP+1, 6):
    pat = [a2 if (i * SP) // SP < num2 or (i % max(1, SP//max(1,num2)) == 0 if num2 else False) else a1 for i in range(SP)]
    # simpler: first num2 hubs a2, rest a1 (block); and interleaved
    pat_block = [a2]*num2 + [a1]*(SP-num2)
    n, e = spine_arms(pat_block, 2)
    Fmix = bethe_density(n, e, 120)
    p = num2/SP
    lin = (1-p)*Fa[a1] + p*Fa[a2]
    print(f"  p(a2)={p:.2f}: F_mix={Fmix:.6f}  linear={lin:.6f}  vs max_endpoint={max(Fa[a1],Fa[a2]):.6f}  "
          f"{'beats a*!' if Fmix > Fa[7]+1e-6 else 'ok<=a*'}")
print(f"\nlog rho* = {LOG_RHO:.6f}; F(a*=7) = {Fa[7]:.6f}")
