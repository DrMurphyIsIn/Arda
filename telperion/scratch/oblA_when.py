"""
When is Aobj(node(A::B::rest)) <= Aobj(node(pushInto A B :: rest)) TRUE?
Scan structured families; report the sign as a function of (deg(A-hub), deg(root), deg(B)).
Key hypothesis: the move helps only when it EQUALIZES, i.e. removing from a HIGH-degree root
and adding to a LOW-degree deep hub. Test high-root, low-hub configs.
"""
import sys
sys.path.insert(0,'/Users/peterwmurphy/repos/Arda-wt-w2a/telperion/scratch')
from oblA_probe import Aobj, pushInto, isPiece, strDefect
from sympy import Rational as R
LEAF=();
def cherry(): return (LEAF,)
def arm(j): return tuple(cherry() for _ in range(j))  # armU j

def test(A,B,rest,label=""):
    before=tuple([A,B]+list(rest)); after=tuple([pushInto(A,B)]+list(rest))
    ab=Aobj(before); af=Aobj(after)
    s='OK ' if af>=ab else 'FAIL'
    print(f"{s} d_root={len(before)} degA_children={len(A)} degB_children={len(B)} : {ab} -> {af}  diff={af-ab}   {label}")

# A = a DEEP-hub spine whose terminal hub is small; root has many piece siblings.
# The deepest hub of pushInto target: A = node[armU k]  (single nonpiece child which is an arm=piece? no arm is piece)
# For pushInto to DESCEND, A needs a nonpiece child. Make A = node[ node[leaf,leaf] ] : spine of depth1, hub=node[leaf,leaf] deg small.
smallhub = (LEAF,LEAF)          # deg-3 node (2 children+parent)
A_deep = (smallhub,)            # node with single nonpiece child -> descends into smallhub
B = (LEAF,LEAF)                 # nonpiece branch

print("== deep hub small, grow root with ARMS (high root deg) ==")
for k in range(0,10):
    test(A_deep, B, [arm(2)]*k, f"rest={k}xarm2")

print("== A already a big hub (many leaves), attach B (direct-hub form) ==")
for hub_leaves in range(2,8):
    A=tuple([LEAF]*hub_leaves)   # hub with many leaf children (nonpiece since not all cherries)
    test(A, B, [], f"A hub {hub_leaves} leaves, no rest")

print("== both A-hub and root large ==")
for hub_leaves in range(2,7):
    for k in range(0,6):
        A=tuple([LEAF]*hub_leaves)
        test(A, B, [arm(1)]*k, f"hub{hub_leaves}L root+{k}")
