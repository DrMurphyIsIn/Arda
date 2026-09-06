from fractions import Fraction as Fr
from a3_derisk import unrooted_Aobj, Ztot_sub, LEAF
import math
RHOB=(621/64)**(1/11); SQRT32=math.sqrt(1.5)
CHERRY=(LEAF,)
def vsize(t): return 1+sum(vsize(c) for c in t)
def caterpillar(m, a=1):
    node=None
    for i in reversed(range(m)):
        arms=tuple([CHERRY]*a)
        node = arms if node is None else arms+(node,)
    return node
print('=== per(L)/prod(deg) [CLASSICAL BG] rate: uniform cherry-caterpillar (a arm/spine vtx) ===')
for a in [1,2]:
  print(f'-- a={a} arms per spine vertex --')
  for m in range(2,14):
    t=caterpillar(m,a); n=vsize(t)
    ar=float(unrooted_Aobj(t))**(1/n); zr=float(Ztot_sub(t))**(1/n)
    print(f' m={m:2d} n={n:2d}  per/deg^(1/n)={ar:.12f}  Ztot_sub^(1/n)={zr:.12f}')
print(f'sqrt(3/2)={SQRT32:.12f}  rhoB={RHOB:.12f}')
print('near-star per/deg^(1/n) (n=2a+1) as a grows:')
for a in [4,5,6,8,10,15,20,40]:
    hub=tuple([CHERRY]*a); n=vsize(hub)
    print(f'  a={a} n={n}: per/deg^(1/n)={float(unrooted_Aobj(hub))**(1/n):.12f}')
