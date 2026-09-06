"""
Is the pushInto/debranch move monotone as a WHOLE-TREE move at a DEEP node,
where the outer tree supplies context? Wrap node(A::B::rest) as a child under
an outer root of varying degree, and measure whole-tree Aobj.
"""
import sys
sys.path.insert(0,'/Users/peterwmurphy/repos/Arda-wt-w2a/telperion/scratch')
from oblA_probe import Aobj, pushInto
from sympy import Rational as R
LEAF=();
def cherry(): return (LEAF,)
def arm(j): return tuple(cherry() for _ in range(j))

A=(LEAF,LEAF); B=(LEAF,LEAF)

def wrap(inner, outer_extra):
    # outer root = node(inner :: outer_extra)
    return tuple([inner]+list(outer_extra))

print("== move at a DEPTH-1 node under an outer root of growing degree ==")
for outer in range(0,8):
    inner_before=tuple([A,B])           # the local site
    inner_after=tuple([pushInto(A,B)])
    extra=[cherry()]*outer
    tb=wrap(inner_before, extra); ta=wrap(inner_after, extra)
    ab=Aobj(tb); af=Aobj(ta)
    print(f"{'OK ' if af>=ab else 'FAIL'} outer_deg={1+outer}: {ab}->{af} diff={af-ab}")

print("== also give the site siblings (rest) AND outer context ==")
for outer in range(0,6):
    for k in range(0,4):
        inner_before=tuple([A,B]+[cherry()]*k)
        inner_after=tuple([pushInto(A,B)]+[cherry()]*k)
        extra=[cherry()]*outer
        tb=wrap(inner_before, extra); ta=wrap(inner_after, extra)
        ab=Aobj(tb); af=Aobj(ta)
        print(f"{'OK ' if af>=ab else 'FAIL'} outer={1+outer} rest={k}: diff={af-ab}")
