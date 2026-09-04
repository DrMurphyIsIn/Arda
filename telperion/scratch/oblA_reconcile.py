"""
Reconcile: Phase-0 genuine cases show straightening RAISES Aobj (+35/54 at n=10).
Those are UNROOTED SPR moves that EQUALIZE degrees.  The Lean pushInto move
CONCENTRATES degree and LOWERS Aobj.  So the Lean-encoded move is the WRONG move:
it is NOT the Phase-0 witness family.

Demonstrate: build the n=10 genuine tree, apply (a) a degree-EQUALIZING SPR (Phase-0
style) and (b) the pushInto-style concentration, and show they move Aobj in OPPOSITE
directions.
"""
import sys
sys.path.insert(0,'/Users/peterwmurphy/repos/Arda-wt-w2a/telperion/scratch')
from oblA_rootinv import perm_L_over_prod, deg, to_edges
from oblA_probe import Aobj, pushInto
from sympy import Rational as R

def val_edges(n,edges): return perm_L_over_prod(n,edges)

# n=10 tree with degseq [3,3,3,3,1,1,1,1,1,1]: a "spider"/branchy tree.
# 4 internal deg-3 vertices in a path 0-1-2-3, each carrying pendants to make degree 3.
# 0:(nbrs 1,p0a,p0b) deg3 ; 1:(0,2,p1) deg3; 2:(1,3,p2) deg3; 3:(2,p3a,p3b) deg3
# vertices: 0,1,2,3 internal; pendants 4,5(on0) 6(on1) 7(on2) 8,9(on3)
edges_before=[(0,1),(1,2),(2,3),(0,4),(0,5),(1,6),(2,7),(3,8),(3,9)]
n=10
d=deg(n,edges_before)
print("before degseq:",sorted(d,reverse=True), "Aobj=",val_edges(n,edges_before))

# Phase-0 EQUALIZING move: remove(0,1) add(1,2)?? doc says remove(0,1)add(1,2) but that keeps a comp;
# The real effect: branch vertex 3->2, spine 1->2.  Emulate: move pendant 4 from vtx0 to a spine end.
# Simpler: take an equalizing move: detach pendant from a deg-3 hub, attach to a deg-1 leaf to extend path.
edges_equalize=[(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(3,8),(3,9),(4,8)]  # moved pendant 4 from 0 to 8 (extends)
d2=deg(n,edges_equalize)
print("equalized degseq:",sorted(d2,reverse=True),"Aobj=",val_edges(n,edges_equalize),
      " (up)" if val_edges(n,edges_equalize)>val_edges(n,edges_before) else " (down)")

# CONCENTRATING move (pushInto-style): take pendant from spine, pile onto an existing deg-3 hub.
edges_concentrate=[(0,1),(1,2),(2,3),(0,4),(0,5),(0,6),(2,7),(3,8),(3,9)]  # moved 6 from vtx1 to vtx0 (0 now deg4)
d3=deg(n,edges_concentrate)
print("concentrated degseq:",sorted(d3,reverse=True),"Aobj=",val_edges(n,edges_concentrate),
      " (up)" if val_edges(n,edges_concentrate)>val_edges(n,edges_before) else " (down)")
