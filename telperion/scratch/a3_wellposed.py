"""
WELL-POSEDNESS: on the genuine cases, is there a move that is BOTH
  (a) strDefect-decreasing (the exact SCAFFOLD measure)  AND
  (b) Aobj-increasing?
And does the path-extension (my clean Aobj-up move) decrease strDefect?

We work on ROOTED nested-tuple UTrees and mirror the exact Lean strDefect.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, LEAF
from fractions import Fraction as Fr

# ---- exact Lean strDefect on rooted UTree (nested tuple; leaf=()) ----
def isLeaf(K): return K==()
def isCherry(K):
    return len(K)==1 and isLeaf(K[0])
def isArm(K):
    return all(isCherry(c) for c in K)   # node cs; cs.all isCherry; empty => True (leaf is arm!)
def isPiece(K): return isArm(K) or isCherry(K)
def npCount(cs): return sum(0 if isPiece(c) else 1 for c in cs)
def strDefect(K):
    cs=K
    npc=npCount(cs)
    local = npc-1 if npc>=1 else 0   # Nat subtraction
    return local + sum(0 if isPiece(c) else strDefect(c) for c in cs)

def gen_trees(n):
    if n==1:
        yield (); return
    def parts(total):
        if total==0:
            yield []; return
        for first in range(1,total+1):
            for T in gen_trees(first):
                for rest in parts(total-first):
                    yield [T]+rest
    seen=set()
    for cs in parts(n-1):
        t=tuple(cs)
        if t not in seen:
            seen.add(t); yield t

# ---- all SPR relocations on a ROOTED UTree, as reparent of a child subtree ----
def to_edges(t):
    edges=[]; nid=[0]
    def rec(node):
        me=nid[0]; nid[0]+=1
        for c in node:
            ch=rec(c); edges.append((me,ch))
        return me
    rec(t); return nid[0], edges

import networkx as nx
def rooted_from(adj, root, parent):
    return tuple(rooted_from(adj,c,root) for c in adj[root] if c!=parent)

def all_spr_rooted(t):
    """Yield rooted UTrees (re-rooted at original root 0) reachable by one edge relocation.
    We generate on the unrooted graph then re-root at node 0 (Aobj root-invariant; strDefect
    uses the SAME root as before for a fair comparison -- root at original global root)."""
    n,edges=to_edges(t)
    G=nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    seen=set(); orig=frozenset(frozenset(e) for e in edges)
    for (u,v) in list(edges):
        H=G.copy(); H.remove_edge(u,v)
        compU=nx.node_connected_component(H,u)
        compV=nx.node_connected_component(H,v)
        for a in compU:
            for b in compV:
                ne=frozenset(frozenset(e) for e in H.edges())|{frozenset((a,b))}
                if ne==orig or ne in seen: continue
                seen.add(ne)
                Gp=nx.Graph(); Gp.add_nodes_from(range(n))
                for e in ne:
                    x,y=tuple(e); Gp.add_edge(x,y)
                if Gp.number_of_edges()==n-1 and nx.is_connected(Gp):
                    adj={i:list(Gp.neighbors(i)) for i in range(n)}
                    yield rooted_from(adj,0,-1)

def min_defect_over_roots(t):
    n,edges=to_edges(t)
    adj={i:[] for i in range(n)}
    for a,b in edges: adj[a].append(b); adj[b].append(a)
    best=None
    for r in range(n):
        rt=rooted_from(adj,r,-1)
        d=strDefect(rt)
        if best is None or d<best: best=d
    return best

def run(maxn=12):
    genuine=0
    have_both=0    # exists SPR move with strDefect-down AND Aobj-up (both measured at min-over-roots for defect)
    none=[]
    for n in range(2,maxn+1):
        for t in gen_trees(n):
            md=min_defect_over_roots(t)
            if md<=0: continue
            genuine+=1
            aT=Aobj_node(t)
            found=False
            for tp in all_spr_rooted(t):
                if min_defect_over_roots(tp)<md and Aobj_node(tp)>=aT:
                    found=True; break
            if found: have_both+=1
            else: none.append((n,t))
    print(f"genuine rooted UTrees n<={maxn} (min strDefect over roots >0): {genuine}")
    print(f"  have an SPR move that BOTH lowers min-strDefect AND does not lower Aobj: {have_both}")
    print(f"  WELL-POSED failures (no such move): {len(none)}")
    for x in none[:8]: print("   NOFIND:",x)

if __name__=="__main__":
    run(int(sys.argv[1]) if len(sys.argv)>1 else 12)

def debranch_moves(t):
    """Apply SCAFFOLD debranchLocal at the ROOT: for the root's children, find node-As (nonpiece,
    non-leaf) at i and B (nonpiece) at j; produce node(node(As++[B]) :: rest). Yield afters."""
    cs=list(t)
    for i in range(len(cs)):
        nodeAs=cs[i]
        if isPiece(nodeAs) or nodeAs==(): continue
        for j in range(len(cs)):
            if j==i: continue
            B=cs[j]
            if isPiece(B): continue
            rest=[cs[k] for k in range(len(cs)) if k!=i and k!=j]
            yield tuple([tuple(list(nodeAs)+[B])]+rest)

def compare(maxn=12):
    genuine=0
    debranch_available=0; debranch_up_and_defectdown=0
    pathext_available=0; pathext_up_and_defectdown=0
    for n in range(2,maxn+1):
        for t in gen_trees(n):
            if strDefect(t)==0: continue   # root-fixed strDefect (the Lean StraightStep is at the root)
            genuine+=1
            aT=Aobj_node(t); dT=strDefect(t)
            # debranchLocal at root
            db=list(debranch_moves(t))
            if db: debranch_available+=1
            if any(strDefect(tp)<dT and Aobj_node(tp)>=aT for tp in db):
                debranch_up_and_defectdown+=1
            # path-extension: move a leaf child of root onto a leaf sibling (extend). Also allow
            # moving a leaf from any child-hub onto a leaf. We approximate via SPR relocations that
            # (a) lower root strDefect and (b) are leaf->leaf pendant moves.  Use all_spr_rooted then
            # filter to strDefect-down & Aobj-up (root-fixed strDefect).
            pe=[tp for tp in all_spr_rooted(t) if strDefect(tp)<dT and Aobj_node(tp)>=aT]
            if pe:
                pathext_up_and_defectdown+=1
    print(f"\n[root-fixed strDefect, StraightStep at root] genuine (strDefect(t)>0): {genuine}")
    print(f"  debranchLocal has a trigger: {debranch_available}")
    print(f"  debranchLocal move that is strDefect-down AND Aobj-up: {debranch_up_and_defectdown}")
    print(f"  SOME SPR move strDefect-down AND Aobj-up (well-posed at root): {pathext_up_and_defectdown}")

if __name__=="__main__" and len(sys.argv)>2 and sys.argv[2]=="cmp":
    compare(int(sys.argv[1]))
