"""Per-cap rates with class credits kappa_j (j = bcc of a NON-atom branch, j=1,2,3):
invariant  bell b + rho b <= -alpha|b| - kappa_{bcc b}  for non-atoms."""
exec(open(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)),"rate4.py")).read().split("L=math.log(26/23)")[0])
import pickle, itertools
def types_k(alpha,D,kap):
    T=[]
    for nm,b,y,bcc,s in AT:
        if bcc>D-1: continue
        beta=-(b+rho(bcc,y)); T.append((nm,y,rho(bcc,y)+beta-alpha*s, nm=="C"))
    for (bcc,lo,hi) in classes(D):
        for y in (lo,hi): T.append((f"N{bcc}",y,rho(bcc,y)+kap.get(bcc,0.0),False))
    return T
def ok_all(alpha,D,kap):
    T=types_k(alpha,D,kap)
    # d=2 exact cell, vertex class bcc=1 pays kap[1]
    m=1e9
    for nm,y,w,isC in T:
        if nm in ("L","C"): continue
        rv=A+(1/(2+y)-1/3)/4
        m=min(m, w-math.log(1+y/2)+F-rv-alpha-kap.get(1,0))
    if m<0: return False
    for d in range(3,D+1):
        if minval(d,alpha,T) - kap.get(d-1,0) < 0: return False
    return True
def alpha_kap(D,kap):
    lo,hi=0.0,0.05
    for it in range(30):
        a=(lo+hi)/2
        if ok_all(a,D,kap): lo=a
        else: hi=a
    return lo
if __name__=="__main__":
    for D in (6,8,12,16,23):
        base=alpha_kap(D,{})
        best=(base,{})
        for k1 in (0,0.01,0.02,0.04):
            for k2 in (0,0.005,0.01,0.02,0.04,0.06):
                for k3 in (0,0.005,0.01,0.02,0.04):
                    kap={1:k1,2:k2,3:k3}; a=alpha_kap(D,kap)
                    if a>best[0]: best=(a,kap)
        print(D,"alpha base",round(base,6),"best",round(best[0],6),best[1],flush=True)
