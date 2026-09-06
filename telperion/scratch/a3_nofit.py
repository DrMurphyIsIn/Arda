"""Characterize the 9 NOFIT genuine cases: what straightening witness works there, and is it
still cleanly signed? Enumerate ALL SPR relocations that lower defect & don't lower Aobj, and
report the STRUCTURE of the moved subtree B and the target v for the best-margin witness."""
from fractions import Fraction as Fr
import networkx as nx
from a3_sweep import Aobj_G, min_defect, spr_relocations, deg

nofits=[
 [(0,1),(0,2),(1,5),(1,9),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12)],
 [(0,1),(0,2),(0,3),(0,4),(1,5),(1,9),(5,6),(5,7),(5,8),(9,10),(9,11),(9,12)],
]
def subtree_shape(T,u,w):
    """describe the subtree hanging at w away from u: (#nodes, is single leaf, is cherry, degree of w)."""
    H=T.copy(); H.remove_edge(u,w)
    comp=nx.node_connected_component(H,w)
    return len(comp), deg(T,w)

for edges in nofits:
    T=nx.Graph(); T.add_edges_from(edges)
    T=nx.convert_node_labels_to_integers(T)
    aT=Aobj_G(T); mdT=min_defect(T)
    best=None
    for Gp,w,u,v in spr_relocations(T):
        du=deg(T,u); dv=deg(T,v)
        aGp=Aobj_G(Gp)
        if aGp<aT: continue
        if min_defect(Gp)>=mdT: continue
        sz,dw=subtree_shape(T,u,w)
        cand=(aGp-aT,du,dv,sz,dw)
        if best is None or cand[0]>best[0]: best=cand
    print(f"nofit n={T.number_of_nodes()}: best witness margin={best[0]} du={best[1]} dv={best[2]} movedSubtreeSize={best[3]} deg(w)={best[4]}")
