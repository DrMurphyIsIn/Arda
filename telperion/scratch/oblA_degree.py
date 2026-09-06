"""Does Obligation A's sign flip with root degree (# siblings)?"""
import sys
sys.path.insert(0, '/Users/peterwmurphy/repos/Arda-wt-w2a/telperion/scratch')
from oblA_probe import Aobj, pushInto, isPiece, strDefect
from sympy import Rational as R

LEAF=()
def cherry(): return (LEAF,)     # ((),)
# spine node A that is the deep hub itself (no nonpiece child): node[leaf,leaf]
A0=(LEAF,LEAF)
B0=(LEAF,LEAF)

# add `k` leaf siblings as rest (leaves are pieces, raise root degree)
for k in range(0,8):
    rest=[LEAF]*k
    before=tuple([A0,B0]+rest)
    after=tuple([pushInto(A0,B0)]+rest)
    ab=Aobj(before); af=Aobj(after)
    print(f"rest={k} leaves  d_root={len(before)} : before={ab}  after={af}  diff={af-ab}  {'OK' if af>=ab else 'FAIL'}")

print("---- rest = cherries instead of leaves ----")
for k in range(0,8):
    rest=[cherry()]*k
    before=tuple([A0,B0]+rest)
    after=tuple([pushInto(A0,B0)]+rest)
    ab=Aobj(before); af=Aobj(after)
    print(f"rest={k} cherries d_root={len(before)} : diff={af-ab}  {'OK' if af>=ab else 'FAIL'}")

print("---- vary A depth (deeper hub), rest=cherries*6 ----")
# A = a spine of depth: node[node[...leaf,leaf...]] etc, B nonpiece
def spine(depth):
    # node[ node[ ... node[leaf,leaf] ] ] with `depth` nesting; each layer one nonpiece child
    t=(LEAF,LEAF)
    for _ in range(depth):
        t=(t,)   # node with single nonpiece child = spine step
    return t
for depth in range(0,4):
    A=spine(depth)
    for k in [0,4,6,10]:
        rest=[cherry()]*k
        before=tuple([A,B0]+rest)
        after=tuple([pushInto(A,B0)]+rest)
        ab=Aobj(before); af=Aobj(after)
        print(f"depth={depth} d_root={len(before)} strDefA={strDefect(A)}: diff={af-ab}  {'OK' if af>=ab else 'FAIL'}")
