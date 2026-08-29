"""Exact cavity (Bethe) free energy for the matching / monomer-dimer model on trees.

Edge weight w_{uv} = 1/(d_u d_v).  Z = sum_matchings prod_{e in M} w_e = per(L)/prod(deg) = prod_{lam>0}(1+lam^2).
Cavity messages on directed edges:
    x_{u->v} = sum_{c ~ u, c != v} w_{uc} / (1 + x_{c->u})            (q_{c->u} = 1/(1+x_{c->u}))
Exact Bethe free energy (exact on trees):
    log Z = sum_v log(1 + sum_{a~v} w_{va} q_{a->v})  -  sum_{(u,v) in E} log(1 + w_{uv} q_{u->v} q_{v->u}).
Verify log Z_Bethe == log(per/prod deg) on all trees n<=8, then compute the caterpillar's fixed point and
its density, confirming F -> log rho*.
"""
import sys, math
from fractions import Fraction as F
sys.path.insert(0, 'telperion/src')
import networkx as nx
from telperion.girardeau import hard_core_boson_partition

RHO = 1.2276458
LOG_RHO = math.log(RHO)


def cavity_messages(n, edges, iters=2000, tol=1e-14):
    d = [0]*n; adj = [[] for _ in range(n)]
    for a, b in edges:
        d[a] += 1; d[b] += 1; adj[a].append(b); adj[b].append(a)
    w = {}
    for a, b in edges:
        w[(a, b)] = w[(b, a)] = 1.0/(d[a]*d[b])
    x = {}
    for a, b in edges:
        x[(a, b)] = x[(b, a)] = 0.0    # directed messages x[(u,v)] = message u->v
    for _ in range(iters):
        mx = 0.0
        newx = {}
        for (u, v) in x:
            s = 0.0
            for c in adj[u]:
                if c == v: continue
                s += w[(u, c)] / (1.0 + x[(c, u)])
            newx[(u, v)] = s
        for k in x:
            mx = max(mx, abs(newx[k]-x[k]))
        x = newx
        if mx < tol: break
    return d, adj, w, x


def bethe_logZ(n, edges):
    d, adj, w, x = cavity_messages(n, edges)
    q = {k: 1.0/(1.0+x[k]) for k in x}
    vsum = 0.0
    for v in range(n):
        a_v = 1.0 + sum(w[(v, a)]*q[(a, v)] for a in adj[v])
        vsum += math.log(a_v)
    esum = 0.0
    seen = set()
    for a, b in edges:
        e = (min(a, b), max(a, b))
        if e in seen: continue
        seen.add(e)
        esum += math.log(1.0 + w[(a, b)]*q[(a, b)]*q[(b, a)])
    return vsum - esum


def edges_of(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return T.number_of_nodes(), [(idx[a], idx[b]) for a, b in T.edges()]


print("=== verify Bethe logZ == log(per/prod deg) over all trees n<=8 ===")
worst = 0.0; tot = 0
for nn in range(2, 9):
    for T in nx.nonisomorphic_trees(nn):
        m, e = edges_of(T); tot += 1
        exact = math.log(float(hard_core_boson_partition(m, e)))
        beth = bethe_logZ(m, e)
        worst = max(worst, abs(exact-beth))
print(f"  {tot} trees, max |logZ_Bethe - log(per/prod)| = {worst:.2e}")


def caterpillar_legs(sp, a, L):
    e = []; nid = sp
    for i in range(sp-1): e.append((i, i+1))
    for i in range(sp):
        for _ in range(a):
            p = i
            for _ in range(L): e.append((p, nid)); p = nid; nid += 1
    return nid, e


print("\n=== caterpillar cavity density (bulk) vs log rho* ===")
for a in (5, 7, 9):
    n, e = caterpillar_legs(60, a, 2)
    F_density = bethe_logZ(n, e)/n
    print(f"  a={a}: F = {F_density:.6f}   (log rho* = {LOG_RHO:.6f})")
