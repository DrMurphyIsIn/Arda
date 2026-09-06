"""
A3 crux: exhaustive genuine-witness sweep of the DEGREE-EQUALIZING SPR move.

For every unrooted tree n<=N, find the genuine non-backbone graphs (min strDefect over
roots > 0).  For each, find a witnessing SPR move that (a) does NOT decrease Aobj and
(b) lowers min-defect, RESTRICTED to the degree-equalizing family: the move relocates a
subtree B from a vertex u to an adjacent-ish vertex v with deg(u) > deg(v) (a *pure leaf/
edge relocation* remove (u,w) add (v,w)).  Report the exact increment and (d_u,d_v).

Aobj computed via exact unrooted per(L)/prod(deg) (root-invariant).
"""
from fractions import Fraction as Fr
import networkx as nx
import sys

def Aobj_edges(n, edges):
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

def Aobj_G(G):
    return Aobj_edges(G.number_of_nodes(), list(G.edges()))

# ---- strDefect over rootings (mirror phase0) ----
def _children(G,v,p): return [w for w in G.neighbors(v) if w!=p]
def isLeaf(G,v,p): return len(_children(G,v,p))==0
def isCherry(G,v,p):
    ch=_children(G,v,p); return len(ch)==1 and isLeaf(G,ch[0],v)
def isArm(G,v,p):
    return all(isCherry(G,c,v) for c in _children(G,v,p))
def isPiece(G,v,p): return isArm(G,v,p) or isCherry(G,v,p)
def strDefect(G,v,p):
    ch=_children(G,v,p)
    nonpiece=[c for c in ch if not isPiece(G,c,v)]
    return max(0,len(nonpiece)-1)+sum(strDefect(G,c,v) for c in nonpiece)
def min_defect(G):
    return min(strDefect(G,r,None) for r in G.nodes())

def spr_relocations(G):
    """Yield (Gp, w, u, v): move the single edge (u,w) -> (v,w): detach pendant-subtree
    hanging off u via w, reattach it to v.  This is the reparent-B-from-u-to-v move.
    We only require the result is a tree.  Return the moved neighbor w and endpoints."""
    nodes=list(G.nodes())
    for (u,w) in list(G.edges()):
        for (uu,ww,udir) in [(u,w,'uw'),(w,u,'wu')]:
            # detach subtree on the ww-side of edge, reattach ww to some v
            H=G.copy(); H.remove_edge(uu,ww)
            compUU=nx.node_connected_component(H,uu)   # side containing uu (the "keeper" root region)
            # ww's subtree = other component; reattach ww to any v in compUU, v != uu
            for v in compUU:
                if v==uu: continue
                Gp=H.copy(); Gp.add_edge(v,ww)
                if Gp.number_of_edges()==len(nodes)-1 and nx.is_connected(Gp):
                    yield Gp, ww, uu, v   # subtree rooted at ww moved from uu to v

def deg(G,x): return G.degree(x)

def run(N=12):
    genuine=0
    equalizing_witnesses=0
    negatives=[]
    zero_margin=[]
    all_margins=[]
    detail=[]
    for n in range(2,N+1):
        for T0 in nx.nonisomorphic_trees(n):
            T=nx.convert_node_labels_to_integers(T0)
            if min_defect(T)<=0: continue
            genuine+=1
            aT=Aobj_G(T)
            mdT=min_defect(T)
            # search degree-equalizing relocations that lower min-defect w/o decreasing Aobj
            best=None
            for Gp,w,u,v in spr_relocations(T):
                # degree-equalizing: BEFORE move deg(u)>deg(v).  After: u loses 1, v gains 1.
                du=deg(T,u); dv=deg(T,v)
                if not (du>dv): continue    # restrict to the equalizing direction
                aGp=Aobj_G(Gp)
                if aGp<aT: continue
                if min_defect(Gp)<mdT:
                    margin=aGp-aT
                    cand=(margin,du,dv,w,u,v,Gp,aGp)
                    if best is None or margin>best[0]:
                        best=cand
            if best is not None:
                equalizing_witnesses+=1
                margin,du,dv,w,u,v,Gp,aGp=best
                all_margins.append(margin)
                if margin<0: negatives.append((n,margin,du,dv))
                if margin==0: zero_margin.append((n,du,dv))
                detail.append((n,margin,du,dv,aT,aGp))
    print(f"N<={N}: genuine non-backbone graphs = {genuine}")
    print(f"  with a DEGREE-EQUALIZING relocation witness (du>dv, Aobj nondecr, defect down): {equalizing_witnesses}")
    print(f"  negative-margin cases: {len(negatives)}   zero-margin (tie) cases: {len(zero_margin)}")
    if all_margins:
        print(f"  min margin = {min(all_margins)}   (strictly>0: {all(m>0 for m in all_margins)})")
    if negatives: print("  NEGATIVES:",negatives[:10])
    if zero_margin: print("  ZEROS:",zero_margin[:10])
    print("  sample (n, margin, du, dv, Aobj_before, Aobj_after):")
    for row in detail[:12]:
        print("   ",row)
    return detail, negatives, zero_margin

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 12
    run(N)

def run_adversarial(N=13):
    """For EVERY genuine tree, look at ALL degree-equalizing relocations (du>dv) that lower
    min-defect, and report the WORST (min) Aobj margin -- not the best.  If even the worst is
    strictly >0, the sign is carried unconditionally by du>dv (no cherry-picking needed)."""
    worst_overall=None
    any_neg=[]; any_zero=[]
    count=0
    for n in range(2,N+1):
        for T0 in nx.nonisomorphic_trees(n):
            T=nx.convert_node_labels_to_integers(T0)
            if min_defect(T)<=0: continue
            aT=Aobj_G(T); mdT=min_defect(T)
            for Gp,w,u,v in spr_relocations(T):
                du=deg(T,u); dv=deg(T,v)
                if not (du>dv): continue
                if min_defect(Gp)>=mdT: continue   # only genuine straightening relocations
                margin=Aobj_G(Gp)-aT
                count+=1
                if margin<0: any_neg.append((n,margin,du,dv))
                if margin==0: any_zero.append((n,du,dv))
                if worst_overall is None or margin<worst_overall[0]:
                    worst_overall=(margin,n,du,dv)
    print(f"\n[ADVERSARIAL over ALL equalizing straightening relocations, N<={N}]")
    print(f"  relocations examined: {count}")
    print(f"  negative-margin: {len(any_neg)}   zero-margin: {len(any_zero)}")
    print(f"  WORST (min) margin over all: {worst_overall}")
    if any_neg: print("  NEG examples:",any_neg[:10])
    if any_zero: print("  ZERO examples:",any_zero[:10])

if __name__=="__main__" and len(sys.argv)>2 and sys.argv[2]=="adv":
    run_adversarial(int(sys.argv[1]))
