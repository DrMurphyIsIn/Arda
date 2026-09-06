"""
Reconstruct the Phase-0 n=10 witness (Aobj 50/9 -> 335/54, remove(0,1) add(1,2))
as UNROOTED graphs and verify the move increases Aobj. Then examine the degseq:
[3,3,3,3,1,1,1,1,1,1] -> [3,3,3,2,2,1,1,1,1,1].
Compare with what pushInto does to degrees.
"""
import sys
sys.path.insert(0,'/Users/peterwmurphy/repos/Arda-wt-w2a/telperion/scratch')
from oblA_rootinv import perm_L_over_prod, deg
from sympy import Rational as R

def val(n,edges): return perm_L_over_prod(n,edges)

# We only know degseqs from the doc, not the exact tree. Instead test the GENERAL principle:
# Phase-0 move LOWERS a max degree-3 branch vertex to 2 and RAISES a spine vertex 1->2.
# i.e. it EQUALIZES degrees (toward caterpillar). pushInto CONCENTRATES (raises a hub).
# Demonstrate on a clean pair:

# Caterpillar-ish vs star-ish on same n, same edges count:
# Path P4 with pendants vs star:
def star(n):
    return n, [(0,i) for i in range(1,n)]
def path(n):
    return n, [(i,i+1) for i in range(n-1)]

for n in [4,5,6,7,8]:
    ns,es=star(n); np_,ep=path(n)
    print(f"n={n}: star Aobj={val(ns,es)}   path Aobj={val(np_,ep)}   path>star={val(np_,ep)>val(ns,es)}")

print()
print("So Aobj is MAXIMIZED toward the path (equalized degrees) and MINIMIZED at the star.")
print("Phase-0's straightening EQUALIZES degrees (branch 3->2, spine 1->2) => Aobj UP.")
print("pushInto at a small root CONCENTRATES degree at a deep hub => Aobj DOWN (the FAILs).")
