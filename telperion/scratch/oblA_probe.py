"""
Obligation A probe. Model the exact UTree cavity recursion (matching Lean R47Tree.lean /
CavityTree.lean) in sympy rationals, then dissect

    Aobj(node (A :: B :: rest)) <= Aobj(node (pushInto A B :: rest)).

Tree encoding: a UTree is a python tuple of children (each a UTree). () = leaf (node []).
"""
from sympy import Rational as R, simplify, symbols, Poly, factor, expand, nsimplify
import itertools, random

# ---- degree ----
def udeg(K):            # non-root degree = #children + 1 (parent edge)
    return len(K) + 1

# ---- cavity partition functions on the *subtree* realization (non-root), degree = udeg ----
# dtSub K = node of degree udeg(K); edge to child C weighted 1/(udeg(K)*udeg(C)).
# We compute (Ztot, Zopen) of dtSub K.
from functools import lru_cache
def _key(K):  # hashable
    return K
def ZtZo_sub(K):
    """Return (Ztot(dtSub K), Zopen(dtSub K)) as sympy Rationals."""
    d = udeg(K)
    # children with weights 1/(d*udeg(C))
    Popen = R(1)   # prod Ztot(child)
    Matched = R(0)
    # Matched = sum_i w_i Zopen(c_i) prod_{j!=i} Ztot(c_j); build via accumulation
    for C in K:
        Zt_c, Zo_c = ZtZo_sub(C)
        w = R(1, d*udeg(C))
        Matched = w*Zo_c*Popen + Zt_c*Matched
        Popen = Zt_c*Popen
    Zopen = Popen
    Ztot = Popen + Matched
    return (Ztot, Zopen)

def Aobj(t):
    """t = node cs (root). Root degree = len(cs); edge to child C weighted 1/(len*udeg C)."""
    cs = t
    d = len(cs)
    Popen = R(1); Matched = R(0)
    for C in cs:
        Zt_c, Zo_c = ZtZo_sub(C)
        w = R(1, d*udeg(C)) if d>0 else R(0)
        Matched = w*Zo_c*Popen + Zt_c*Matched
        Popen = Zt_c*Popen
    return Popen + Matched

# ---- pushInto (matching R47R7PushInto.lean) ----
def isCherry(K):   # node [leaf] i.e. ((),)  -> a single leaf child
    return K == ((),)
def isLeaf(K):
    return K == ()
def isArm(K):
    # arm = node whose every child is a cherry (Lean: cs.all isCherry; leaf -> vacuous true)
    return all(isCherry(c) for c in K)
def isPiece(K):
    return isArm(K) or isCherry(K)

def npCount(cs):
    return sum(0 if isPiece(c) else 1 for c in cs)
def npDefectSum(cs):
    return sum(0 if isPiece(c) else strDefect(c) for c in cs)
def strDefect(t):
    cs=t
    return (npCount(cs)-1 if npCount(cs)>=1 else 0) + npDefectSum(cs)  # Nat subtraction

def pushInto(A, B):
    return tuple(pushIntoList(list(A), B))
def pushIntoList(As, B):
    if not As:
        return [B]
    c, rest = As[0], As[1:]
    if isPiece(c):
        return [c] + pushIntoList(rest, B)
    else:
        return [pushInto(c, B)] + rest

# ---------------- Phase-0 replication: strict margin over small trees ----------------
def gen_trees(n):
    """all rooted trees with n nodes (as nested tuples), up to child-order (we keep all orders small)."""
    if n == 1:
        yield ()
        return
    # partition n-1 nodes among an ordered list of children
    def parts(total):
        # ordered compositions into subtrees
        if total == 0:
            yield []
            return
        for first in range(1, total+1):
            for T in gen_trees(first):
                for restcs in parts(total-first):
                    yield [T]+restcs
    seen=set()
    for cs in parts(n-1):
        t=tuple(cs)
        if t not in seen:
            seen.add(t)
            yield t

def run_phase0(maxn=8):
    fails=0; strict=0; ties=0; tested=0
    for n in range(3, maxn+1):
        for t in gen_trees(n):
            cs=list(t)
            if len(cs)<2: continue
            # try all (A,B,rest) with A nonpiece, strDefect(A)==0-ish, B nonpiece
            for i in range(len(cs)):
                for j in range(len(cs)):
                    if i==j: continue
                    A=cs[i]; B=cs[j]
                    if isPiece(A) or isPiece(B): continue
                    if strDefect(A)!=0: continue   # Obligation A precondition: A spine-like
                    rest=[cs[k] for k in range(len(cs)) if k!=i and k!=j]
                    before=tuple([A,B]+rest)
                    after=tuple([pushInto(A,B)]+rest)
                    ab=Aobj(before); af=Aobj(after)
                    tested+=1
                    if af<ab: fails+=1; print("FAIL",n,before,ab,af)
                    elif af==ab: ties+=1
                    else: strict+=1
    print(f"tested={tested} strict={strict} ties={ties} FAILS={fails}")

if __name__=="__main__":
    run_phase0(8)
