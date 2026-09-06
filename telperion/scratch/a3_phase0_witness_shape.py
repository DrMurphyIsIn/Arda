"""Among the 30 GENUINE cases, does a PATH-EXTENSION witness (move a single leaf w from hub u
onto a LEAF v, dv=1) always exist with strict Aobj increase and defect drop?  This is the
cleanest A3.  If yes, A3 reduces to the single-pendant path-extension inequality."""
from fractions import Fraction as Fr
import networkx as nx
from a3_sweep import Aobj_G, min_defect, deg

def leaf_to_leaf_witnesses(T):
    """Move a leaf w (deg 1, neighbor u) to a leaf v (deg 1, v!=w, v not adjacent to w's u
    trivially). Result must be tree, lower min-defect, Aobj nondecreasing."""
    aT=Aobj_G(T); mdT=min_defect(T)
    outs=[]
    leaves=[x for x in T.nodes() if deg(T,x)==1]
    for w in leaves:
        u=next(iter(T.neighbors(w)))
        du=deg(T,u)
        for v in leaves:
            if v==w or v==u: continue
            dv=deg(T,v)  # =1
            if not (du>dv): continue
            H=T.copy(); H.remove_edge(u,w); H.add_edge(v,w)
            if H.number_of_edges()!=T.number_of_nodes()-1 or not nx.is_connected(H): continue
            aH=Aobj_G(H)
            if aH<aT: continue
            if min_defect(H)<mdT:
                outs.append((aH-aT,u,v,w,du))
    return aT,mdT,outs

def run(N=14):
    genuine=0; have_pathext=0; strict=0; fails=[]
    for n in range(2,N+1):
        for T0 in nx.nonisomorphic_trees(n):
            T=nx.convert_node_labels_to_integers(T0)
            if min_defect(T)<=0: continue
            genuine+=1
            aT,mdT,outs=leaf_to_leaf_witnesses(T)
            if outs:
                have_pathext+=1
                if all(o[0]>0 for o in outs) and any(o[0]>0 for o in outs): strict+=1
            else:
                fails.append((n, sorted(tuple(sorted(e)) for e in T.edges())))
    print(f"N<={N}: genuine={genuine}")
    print(f"  have a single-leaf->leaf PATH-EXTENSION straightening witness: {have_pathext}")
    print(f"  (of those, every such witness strictly raises Aobj): {strict}")
    print(f"  genuine cases with NO leaf->leaf path-ext witness: {len(fails)}")
    for f in fails[:8]: print("   NOFIT:",f)
if __name__=="__main__":
    run(14)
