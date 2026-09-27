import math, sys
import numpy as np
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..'))
import bg_spider_reduction as B
F=B.F; A=B.ANCHOR
AT=B.atoms_float(22)   # arms j<=22 (degree cap 23)
def rho(bcc,y): return B.rho_wit(bcc,y)
# child types: atoms (exact) and non-atom classes with y-ranges (sampled finely)
def child_types(alpha):
    T=[]
    for nm,b,y,bcc,s in AT:
        beta=-(b+rho(bcc,y))
        T.append((nm,y,rho(bcc,y)+beta-alpha*s, nm=="C"))
    for (bcc,lo,hi) in [(1,0.4,0.5),(2,0.0,1/3),(3,0.0,0.25),(4,0.0,0.2)]:
        for y in np.linspace(lo,hi,41):
            T.append((f"N{bcc}",y,rho(bcc,y),False))
    return T
def minval(d,alpha,T):
    """lower bound of min over non-atom configs with d-1 children of
       sum w_c - log(1+S/d) + F* - rho(v) - alpha, via tangent at S0 (max over S0)."""
    K=d-1
    best=-1e9
    for S0 in np.linspace(0,K*0.5,120):
        sig=1/(d+S0)
        c0=-(math.log(1+S0/d)-sig*S0)
        vals=[(w-sig*y,isC) for nm,y,w,isC in T]
        mall=min(v for v,_ in vals); mnc=min(v for v,isC in vals if not isC)
        # rho(v): for K>=4 zero; for K<=3 upper bound rho(v) <= its max
        rv={0:F,1:A+(1/2-1/3)/4,2:1/96,3:1/1536}.get(K,0.0)
        lb=(K-1)*mall+mnc+c0+F-rv-alpha if K>=1 else None
        best=max(best,lb)
    return best
lo,hi=0.0,0.002
for it in range(30):
    a=(lo+hi)/2; T=child_types(a)
    ok=all(minval(d,a,T)>=0 for d in range(2,24))
    if ok: lo=a
    else: hi=a
print("alpha ~",lo)
T=child_types(lo)
for d in range(2,24): print(d, "%.5f"%minval(d,lo,T))
