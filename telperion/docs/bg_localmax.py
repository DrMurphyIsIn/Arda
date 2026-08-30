"""Lead 3 analytic step: the caterpillar is a STRICT LOCAL MAX of the exact cavity density in EVERY
independent structural direction -- the second-variation-negative property.  In the cavity method this is
implied by BP fixed-point STABILITY = the strong contraction (W15).  Test: perturb the uniform a=7 length-2
caterpillar in many distinct directions; F must strictly decrease in each (local max).
"""
import math

def bethe_density(n, edges, iters=150):
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


class Builder:
    def __init__(self, spine): self.e = []; self.nid = spine; self.spine = spine
    def arm(self, hub, length):
        p = hub
        for _ in range(length):
            self.e.append((p, self.nid)); p = self.nid; self.nid += 1
        return p


def caterpillar(spine, arms, arm_len=2, perturb=None):
    """uniform caterpillar; perturb = ('type', hub_index) applies a single local change at mid-spine."""
    b = Builder(spine)
    for i in range(spine-1):
        b.e.append((i, i+1))
    mid = spine//2
    for i in range(spine):
        a = arms
        L = arm_len
        if perturb and i == mid:
            typ = perturb
            if typ == 'plus_arm': a = arms+1
            elif typ == 'minus_arm': a = arms-1
            elif typ == 'long_arm':  # one arm length 3
                for _ in range(arms-1): b.arm(i, 2)
                b.arm(i, 3); continue
            elif typ == 'short_arm':  # one arm length 1 (single leaf)
                for _ in range(arms-1): b.arm(i, 2)
                b.arm(i, 1); continue
            elif typ == 'spine_branch':  # extra spine neighbour (a 3-way spine)
                tail = b.arm(i, 5)  # a length-5 branch off the hub ~ another spine
                for _ in range(arms): b.arm(i, 2)
                continue
            elif typ == 'cherry_end':  # one arm ends in a cherry (deg-2 end -> two leaves)
                for _ in range(arms-1): b.arm(i, 2)
                p = b.arm(i, 2); b.arm(p, 1)  # extra leaf at the arm end
                continue
        for _ in range(a):
            b.arm(i, L)
    return b.nid, b.e


F0 = bethe_density(*caterpillar(40, 7, 2))
print(f"uniform a=7 length-2 caterpillar: F0 = {F0:.6f}   (log rho* = {math.log(1.2276458):.6f})")
print("\nsingle-site structural perturbations (F must DROP -> strict local max):")
for typ in ['plus_arm', 'minus_arm', 'long_arm', 'short_arm', 'spine_branch', 'cherry_end']:
    n, e = caterpillar(40, 7, 2, perturb=typ)
    F = bethe_density(n, e)
    print(f"  {typ:14s}: F = {F:.6f}   dF = {F-F0:+.3e}   {'DROP (ok)' if F < F0 else '*** INCREASE ***'}")
