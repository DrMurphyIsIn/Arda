"""Root size-knapsack with rate-envelope children: atom child of size s: exact bell + mu*y;
non-atom child of size s: max_class(-rho - kappa + mu*y) - alpha*s  (from the per-cap rate invariant)."""
exec(open(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)),"rate5.py")).read().split('if __name__=="__main__":')[0])
import pickle, numpy as np
res6=pickle.load(open("rate6_res.pkl","rb"))
sp=pickle.load(open("spider_cache_520.pkl","rb")); phisp={n:math.log(v[0])-(n-1)*F for n,v in sp.items()}
NEG=-1e30; Nmax=520
grid=np.concatenate([np.linspace(0.005,0.08,76),np.linspace(0.085,0.5,84)])
worst={}
for k in range(2,24):
    al,kap,_,_=res6[k]
    atoms=[(s,b,y) for nm,b,y,bcc,s in AT if bcc<=k-1]
    cls=[(y,-rho(bcc,y)-kap.get(bcc,0)) for (bcc,lo,hi) in classes(k) for y in (lo,hi)]
    H=len(grid)
    Wa=np.full((Nmax+1,H),NEG); Wn=np.full((Nmax+1,H),NEG)
    for s,b,y in atoms:
        if s<=Nmax: Wa[s]=np.maximum(Wa[s],b+grid*y)
    nb=np.max(np.array([w+grid*y for y,w in cls]),axis=0)
    for s in range(3,Nmax+1): Wn[s]=nb-al*s     # non-atom branches have size>=3
    FA,FN=pickle.load(open(f"fr_170_{k-1}.pkl" if k in (7,8,9) else f"fr_120_{k-1}.pkl","rb"))
    for s in range(1,max(FA)+1):
        if s in FN:
            l,y=FN[s]; ex=np.max(l[:,None]+grid[None,:]*y[:,None],axis=0); Wn[s]=np.minimum(Wn[s],ex)
    Wall=np.maximum(Wa,Wn)
    # knapsack k parts, >=1 non-atom
    A=np.full((Nmax+1,H),NEG); A[0]=0; Bn=np.full((Nmax+1,H),NEG)
    for i in range(k):
        A2=np.full((Nmax+1,H),NEG); B2=np.full((Nmax+1,H),NEG)
        for s in range(1,Nmax+1):
            A2[s:]=np.maximum(A2[s:],A[:Nmax+1-s]+Wall[s]); B2[s:]=np.maximum(B2[s:],Bn[:Nmax+1-s]+Wall[s])
            B2[s:]=np.maximum(B2[s:],A[:Nmax+1-s]+Wn[s])
        A,Bn=A2,B2
    t=1/(k*grid); val=np.log(t)+1/t-1+Bn; best=np.min(val,axis=1)
    fails=[n for n in range(k+1,Nmax+1) if best[n-1]>=phisp[n]]
    print(f"k={k:2d}: root-knapsack rate bound fails for n in {fails[:6]}{'...' if len(fails)>6 else ''} max fail n={max(fails) if fails else None}",flush=True)
    worst[k]=max(fails) if fails else 0
print("N1 (knapsack) =",max(worst.values())+1)
