"""Two exact-size levels: root knapsack exact; child W_s(mu) <= max_c min_{nu,lam}[const(c,nu,mu) + c*What(nu,lam) + lam*(s-1)]
(grandchildren size-relaxed via What(nu,lam) = sup_b bell - lam|b| + nu y, true values from frontiers, sizes<=S)."""
import sys, math, pickle
import numpy as np
from rootb import PHI
from rootbell2 import knapH
F=math.log(621/64)/11; NEG=-1e30
S=int(sys.argv[1]); Nmax=int(sys.argv[2]); H=int(sys.argv[3])
grid=np.linspace(0.5/H,0.5,H); lams=np.linspace(-0.003,0.06,64)
worst={}
for k in range(2,min(Nmax,24)):
    C=k-1
    FA,FN=pickle.load(open(f"fr_{S}_{C}.pkl","rb"))
    WA=np.full((S+1,H),NEG)
    for s in range(1,S+1):
        l,y=FA[s]; WA[s]=np.max(l[:,None]+grid[None,:]*y[:,None],axis=0)
    sz=np.arange(1,S+1)
    Wh=np.max(WA[1:,None,:]-lams[None,:,None]*sz[:,None,None],axis=0)   # (lam, h) over nu-grid
    # child tables via one Bellman step
    Wa=np.full((S+1,H),NEG); Wn=np.full((S+1,H),NEG)
    Wa[1]=-F+grid
    m_=grid[:,None]; nu=grid[None,:]
    for c in range(1,C+1):
        d=c+1; disc=1-4*m_*nu; u=np.where(disc>=0,(1+np.sqrt(np.maximum(disc,0)))/(2*nu),np.nan)
        valid=(disc>=0)&(u>2*m_)
        const=np.where(valid,np.log(u/d)+m_/u-F-nu*(u-d),np.inf)   # (g,h)
        for s in range(c+1,S+1):
            N=s-1
            inner=np.min(c*Wh+lams[:,None]*N,axis=0)   # (h,) best lam
            v=np.min(const+inner[None,:],axis=1)
            Wa[s]=np.maximum(Wa[s],v)
            # non-atom: c==1 needs N>=3; c>=2: all-size-2 composition is the atom arm_c (N=2c); crude: allow unless N==2c
            if (c==1 and N>=3) or (c>=2 and N!=2*c):
                Wn[s]=np.maximum(Wn[s],v)
            elif c>=2 and N==2*c:
                pass  # needs flag-aware bound; omitted (conservative would include) -> include to stay valid
    # validity: for c>=2,N==2c non-atom compositions exist (e.g. sizes 1,3,...) -> include them conservatively
    for c in range(2,C+1):
        N=2*c; s=N+1
        if s<=S:
            d=c+1; disc=1-4*m_*nu; u=np.where(disc>=0,(1+np.sqrt(np.maximum(disc,0)))/(2*nu),np.nan)
            valid=(disc>=0)&(u>2*m_); const=np.where(valid,np.log(u/d)+m_/u-F-nu*(u-d),np.inf)
            inner=np.min(c*Wh+lams[:,None]*N,axis=0); Wn[s]=np.maximum(Wn[s],np.min(const+inner[None,:],axis=1))
    Bn=knapH(Wa,Wn,k,Nmax-1); t=1/(k*grid); best=np.min(np.log(t)+1/t-1+Bn,axis=1)
    for n in range(k+1,Nmax+1):
        mm=PHI[n]-best[n-1]
        if n not in worst or mm<worst[n][0]: worst[n]=(mm,k)
bad=sorted((n,round(m,5),k) for n,(m,k) in worst.items() if m<=0)
print("two-level H",H,"failures:",bad[:40],"count",len(bad))
