"""Dissect: WHICH degree-equalizing relocations raise Aobj vs lower it?
Hypotheses to test on the negatives:
 (H1) sign depends on whether v is adjacent to u (the true 'sibling/parent-child local'
      move) vs v far away.
 (H2) sign depends on whether the moved neighbor w is a LEAF/piece vs a heavy subtree.
 (H3) the true move relocates B to a vertex v ON THE PATH from u so degrees equalize the
      SPINE -- i.e. v is the lower-degree neighbor of u, and the sign is carried by a LOCAL
      2-vertex reparent (u--v edge exists)."""
from fractions import Fraction as Fr
import networkx as nx
from a3_sweep import Aobj_G, min_defect, spr_relocations, deg

def classify(N=13):
    stats={}   # (v_adj_u, w_is_leaf) -> [pos,neg,zero]
    for n in range(2,N+1):
        for T0 in nx.nonisomorphic_trees(n):
            T=nx.convert_node_labels_to_integers(T0)
            if min_defect(T)<=0: continue
            aT=Aobj_G(T); mdT=min_defect(T)
            for Gp,w,u,v in spr_relocations(T):
                du=deg(T,u); dv=deg(T,v)
                if not (du>dv): continue
                if min_defect(Gp)>=mdT: continue
                margin=Aobj_G(Gp)-aT
                v_adj_u = T.has_edge(u,v)
                w_leaf = (deg(T,w)==1)
                key=(v_adj_u, w_leaf)
                s=stats.setdefault(key,[0,0,0])
                if margin>0: s[0]+=1
                elif margin<0: s[1]+=1
                else: s[2]+=1
    print("key=(v_adjacent_to_u, moved_w_is_leaf) -> [pos,neg,zero]")
    for k,v in sorted(stats.items()):
        print("  ",k,"->",v)

# Sharper: restrict to v ADJACENT to u AND w a leaf-pendant (the pure 'local reparent of a
# pendant from hub u to its lower-degree neighbor v').  Is THAT always positive?
def local_only(N=14):
    pos=neg=zero=0; worst=None; examples=[]
    for n in range(2,N+1):
        for T0 in nx.nonisomorphic_trees(n):
            T=nx.convert_node_labels_to_integers(T0)
            aT=Aobj_G(T)
            for Gp,w,u,v in spr_relocations(T):
                du=deg(T,u); dv=deg(T,v)
                if not (du>dv): continue
                if not T.has_edge(u,v): continue     # v adjacent to u
                margin=Aobj_G(Gp)-aT
                if margin>0: pos+=1
                elif margin<0:
                    neg+=1
                    if worst is None or margin<worst[0]: worst=(margin,n,du,dv,deg(T,w))
                else: zero+=1
    print(f"\n[LOCAL reparent: v adjacent to u, du>dv, ANY moved subtree, N<={N}]")
    print(f"  pos={pos} neg={neg} zero={zero}  worst_neg={worst}")

def local_leaf_only(N=15):
    """v adjacent to u, du>dv, moved w is a LEAF (pure pendant relocation)."""
    pos=neg=zero=0; worst=None
    for n in range(2,N+1):
        for T0 in nx.nonisomorphic_trees(n):
            T=nx.convert_node_labels_to_integers(T0)
            aT=Aobj_G(T)
            for Gp,w,u,v in spr_relocations(T):
                du=deg(T,u); dv=deg(T,v)
                if not (du>dv): continue
                if not T.has_edge(u,v): continue
                if deg(T,w)!=1: continue
                margin=Aobj_G(Gp)-aT
                if margin>0: pos+=1
                elif margin<0:
                    neg+=1
                    if worst is None or margin<worst[0]: worst=(margin,n,du,dv)
                else: zero+=1
    print(f"\n[LOCAL LEAF reparent: v adj u, du>dv, w leaf, N<={N}]  pos={pos} neg={neg} zero={zero} worst={worst}")

if __name__=="__main__":
    classify(13)
    local_only(13)
    local_leaf_only(15)
