"""Class credits for ALL classes incl. bcc>=4 (kappa_4), then root knapsack with exact atoms (rate7-style)."""
exec(open(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)),"rate4.py")).read().split("L=math.log(26/23)")[0])
import pickle
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
    m=1e9
    for nm,y,w,isC in T:
        if nm in ("L","C"): continue
        rv=A+(1/(2+y)-1/3)/4
        m=min(m, w-math.log(1+y/2)+F-rv-alpha-kap.get(1,0))
    if m<0: return False
    for d in range(3,D+1):
        if minval(d,alpha,T) - kap.get(min(d-1,4),0) < 0: return False
    return True
def alpha_kap(D,kap):
    lo,hi=0.0,0.05
    for it in range(28):
        a=(lo+hi)/2
        if ok_all(a,D,kap): lo=a
        else: hi=a
    return lo
sp=pickle.load(open("spider_cache_520.pkl","rb")); phisp={n:math.log(v[0])-(n-1)*F for n,v in sp.items()}
NEG=-1e30; Nmax=520
grid=np.concatenate([np.linspace(0.005,0.08,76),np.linspace(0.085,0.5,84)]); H=len(grid)
def thresh(k,al,kap):
    atoms=[(s,b,y) for nm,b,y,bcc,s in AT if bcc<=k-1]
    cls=[(y,-rho(bcc,y)-kap.get(bcc,0)) for (bcc,lo,hi) in classes(k) for y in (lo,hi)]
    Wa=np.full((Nmax+1,H),NEG); Wn=np.full((Nmax+1,H),NEG)
    for s,b,y in atoms:
        if s<=Nmax: Wa[s]=np.maximum(Wa[s],b+grid*y)
    nb=np.max(np.array([w+grid*y for y,w in cls]),axis=0)
    for s in range(3,Nmax+1): Wn[s]=nb-al*s
    Wall=np.maximum(Wa,Wn)
    A_=np.full((Nmax+1,H),NEG); A_[0]=0; Bn=np.full((Nmax+1,H),NEG)
    for i in range(k):
        A2=np.full((Nmax+1,H),NEG); B2=np.full((Nmax+1,H),NEG)
        for s in range(1,Nmax+1):
            A2[s:]=np.maximum(A2[s:],A_[:Nmax+1-s]+Wall[s]); B2[s:]=np.maximum(B2[s:],np.maximum(Bn[:Nmax+1-s]+Wall[s],A_[:Nmax+1-s]+Wn[s]))
        A_,Bn=A2,B2
    t=1/(k*grid); best=np.min(np.log(t)+1/t-1+Bn,axis=1)
    fails=[n for n in range(k+1,Nmax+1) if best[n-1]>=phisp[n]]
    return max(fails) if fails else 0
if __name__=="__main__":
    ks=[int(x) for x in sys.argv[1].split(",")]
    for k in ks:
        best=None
        for k4 in (0,0.002,0.004,0.006,0.008):
            for k23 in (0.005,0.01):
                kap={1:0.0 if k>6 else 0.004,2:k23,3:k23,4:k4}
                a=alpha_kap(k,kap)*0.95
                if a<=0: continue
                th=thresh(k,a,kap)
                if best is None or th<best[0]: best=(th,a,kap)
        print(f"k={k}: threshold {best[0]} alpha={best[1]:.6f} kap={best[2]}",flush=True)
