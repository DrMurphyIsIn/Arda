"""
A3 crux de-risk for the DEGREE-EQUALIZING SPR move (RealObligationA).

Mirrors the EXACT Lean cavity engine (R47Tree.lean / CavityTree.lean / R47RootRate.lean):

  UTree = node cs  (cs a list of children; leaf = node []).
  udeg(K)          = len(children K) + 1          (subtree degree, incl. parent edge)
  dtSub K          : realize K at degree udeg(K); child edge weight 1/(udeg(K)*udeg(C))
  Zopen(dtSub K)   = prod_C Ztot(dtSub C)                          (P, root unmatched)
  Ztot (dtSub K)   = Zopen + sum_i w_i Zopen(C_i) prod_{j!=i} Ztot(C_j)
  Aobj(node cs)    = Ztot realized at ROOT degree k=len(cs)  (no parent edge)

  Root-degree factorization (Ztot_node_deg):
     Ztot(node cs realized at degree k) = P * (1 + qSum(cs)/k),
       P        = prod_C Ztot(dtSub C)
       qSum(cs) = sum_C  Zopen(dtSub C)/Ztot(dtSub C) / udeg(C)
     -- P and qSum depend ONLY on the children's internal structure, NOT on k.

MOVE (degree-equalizing SPR): a subtree B currently a child of a HIGH-degree vertex u
(root-child-count / degree d_u) is relocated to become a child of a LOWER-degree adjacent
vertex v (degree d_v), with d_u > d_v.  Everything else fixed.  We compute
Aobj(after) - Aobj(before) EXACTLY (fractions) and factor it.

Exact rational arithmetic (fractions.Fraction).
"""
from __future__ import annotations
from fractions import Fraction as Fr
from functools import lru_cache
import itertools

LEAF = ()  # node []

# ------------------------------------------------------------------ cavity engine
def udeg(K):
    return len(K) + 1

@lru_cache(maxsize=None)
def ZtZo_sub(K):
    """(Ztot(dtSub K), Zopen(dtSub K)) as Fractions.  dtSub K realized at degree udeg(K)."""
    d = udeg(K)
    Popen = Fr(1)     # prod Ztot(child)
    Matched = Fr(0)   # leave-one-out matched sum
    for C in K:
        Zt_c, Zo_c = ZtZo_sub(C)
        w = Fr(1, d * udeg(C))
        Matched = w * Zo_c * Popen + Zt_c * Matched
        Popen = Zt_c * Popen
    return (Popen + Matched, Popen)

def Ztot_sub(K):  return ZtZo_sub(K)[0]
def Zopen_sub(K): return ZtZo_sub(K)[1]

def qContrib(C):
    """One child's contribution to qSum:  Zopen(dtSub C)/Ztot(dtSub C)/udeg(C)."""
    Zt, Zo = ZtZo_sub(C)
    return Zo / Zt / udeg(C)

def qSum(cs):
    return sum((qContrib(C) for C in cs), Fr(0))

def P_of(cs):
    """P = prod_C Ztot(dtSub C)."""
    p = Fr(1)
    for C in cs:
        p *= Ztot_sub(C)
    return p

def Aobj_node(cs):
    """Aobj(node cs) = Ztot realized at ROOT degree k = len(cs) = P*(1+qSum/k)."""
    cs = tuple(cs)
    k = len(cs)
    if k == 0:
        return Fr(1)   # leaf root
    return P_of(cs) * (1 + qSum(cs) / k)

# cross-check: direct Ztot realization at arbitrary degree k
def Ztot_at_degree(cs, k):
    cs = tuple(cs)
    Popen = Fr(1); Matched = Fr(0)
    for C in cs:
        Zt_c, Zo_c = ZtZo_sub(C)
        w = Fr(1, k * udeg(C)) if k > 0 else Fr(0)
        Matched = w * Zo_c * Popen + Zt_c * Matched
        Popen = Zt_c * Popen
    return Popen + Matched

def _selfcheck_factor():
    import random
    rng = random.Random(1)
    def rnd_tree(depth):
        if depth == 0 or rng.random() < 0.4:
            return LEAF
        return tuple(rnd_tree(depth-1) for _ in range(rng.randint(1,3)))
    for _ in range(400):
        cs = tuple(rnd_tree(3) for _ in range(rng.randint(1,4)))
        k = rng.randint(1,7)
        lhs = Ztot_at_degree(cs, k)
        rhs = P_of(cs) * (1 + qSum(cs)/k)
        assert lhs == rhs, (cs, k, lhs, rhs)
        # Aobj matches degree = len
        assert Aobj_node(cs) == Ztot_at_degree(cs, len(cs))
    print("[selfcheck] Ztot_node_deg factorization exact on 400 random trees; Aobj matches.  OK")

if __name__ == "__main__":
    _selfcheck_factor()

# =====================================================================================
# WHOLE-TREE SPR (degree-equalizing) MOVE + exact increment factorization.
# =====================================================================================
# We model the whole rooted UTree.  A move relocates subtree B from parent u to parent v.
# We compute Aobj of the whole tree before/after EXACTLY.  To FACTOR the increment we use
# the local structure at u and v.
#
# GENERAL WHOLE-TREE Aobj: node-recursive.  For any rooted UTree we can compute Aobj by
# Aobj_node(cs).  For an internal (non-root) node we use Ztot_sub / Zopen_sub.

# ---- generic rooted-tree manipulation as nested tuples ----
def replace_child(node, idx, newchild):
    lst = list(node); lst[idx] = newchild; return tuple(lst)

def add_child(node, child):
    return tuple(list(node) + [child])

def remove_child(node, idx):
    lst = list(node); del lst[idx]; return tuple(lst)

# ---- recognizers (mirror Lean strDefect) ----
def isCherry(K): return K == (LEAF,)
def isArm(K):    return all(isCherry(c) for c in K)
def isPiece(K):  return isArm(K) or isCherry(K)
def npCount(cs): return sum(0 if isPiece(c) else 1 for c in cs)
def strDefect(K):
    cs = K
    nonpiece = [c for c in cs if not isPiece(c)]
    local = max(0, len(nonpiece) - 1)
    return local + sum(strDefect(c) for c in nonpiece)

# ---- exact unrooted per(L)/prod(deg) for cross-checking root-invariance ----
def to_edges(t):
    edges=[]; nid=[0]
    def rec(node):
        me=nid[0]; nid[0]+=1
        for c in node:
            ch=rec(c); edges.append((me,ch))
        return me
    rec(t)
    return nid[0], edges

def unrooted_Aobj(t):
    n, edges = to_edges(t)
    d=[0]*n
    for a,b in edges: d[a]+=1; d[b]+=1
    E=[(a,b,Fr(1,d[a]*d[b])) for a,b in edges]
    m=len(E); total=Fr(0)
    def rec(i, used, acc):
        nonlocal total
        if i==m: total+=acc; return
        rec(i+1, used, acc)
        a,b,w=E[i]
        if a not in used and b not in used:
            rec(i+1, used|{a,b}, acc*w)
    rec(0,set(),Fr(1))
    return total

def all_rerootings(t):
    n, edges = to_edges(t)
    adj={i:[] for i in range(n)}
    for a,b in edges: adj[a].append(b); adj[b].append(a)
    def build(root,parent):
        return tuple(build(c,root) for c in adj[root] if c!=parent)
    return [build(r,-1) for r in range(n)]

def _selfcheck_rootinv():
    tests=[(LEAF,LEAF),((LEAF,),(LEAF,)),((LEAF,LEAF),(LEAF,LEAF)),
           ((LEAF,LEAF),(LEAF,LEAF),(LEAF,)),((( LEAF,),(LEAF,)),(LEAF,LEAF),(LEAF,))]
    for t in tests:
        u=unrooted_Aobj(t)
        vals=set(Aobj_node(rt) for rt in all_rerootings(t))
        assert len(vals)==1 and next(iter(vals))==u, (t,u,vals)
    print("[selfcheck] Aobj_node root-invariant & equals unrooted per(L)/prod(deg).  OK")

if __name__ == "__main__":
    _selfcheck_rootinv()
