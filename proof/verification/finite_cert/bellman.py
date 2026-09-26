"""Scalar Bellman upper bound for the per-size envelope W_s(mu) = max_{|b|=s} bell(b)+mu*y_b, with degree cap.
At a vertex with c children (d=c+1): V_mu(b) <= [log(u/d) + mu/u - F* - nu*(u-d)] + sum_children V_nu(child),
where u = d+Y0 and nu = 1/u - mu/u^2 (tangent of the concave phi(Y)=log(d+Y)+mu/(d+Y)).  nu is taken on the
same grid as mu (u solved from nu), so no interpolation is needed."""
import sys, math, pickle, time
import numpy as np
F=math.log(621/64)/11
NEG=-1e30
def bellman(S, C, grid):
    """C = max children per vertex. Returns Wa[s,g], Wn[s,g] (non-atom), s=0..S."""
    H=len(grid); mu=np.asarray(grid)
    Wa=np.full((S+1,H),NEG); Wn=np.full((S+1,H),NEG)
    Wa[1]=-F+mu                     # leaf
    # knapsack tables: K[c][N,h] best sum of c parts with sizes summing N (all parts), Kx[c][N,h]: >=1 part != 2
    K=[None]+[np.full((S+1,H),NEG) for _ in range(C)]
    Kx=[None]+[np.full((S+1,H),NEG) for _ in range(C)]
    def upd(N):
        # fill K[c][N], Kx[c][N] for c=1..C using W sizes < = N
        K[1][N]=Wa[N]; Kx[1][N]=Wa[N] if N!=2 else NEG
        for c in range(2,C+1):
            if N<c: break
            m=np.arange(1,N-c+2)          # size of last part
            prev=K[c-1][N-m]; prevx=Kx[c-1][N-m]; w=Wa[m]
            K[c][N]=np.max(prev+w,axis=0)
            w_is2=(m==2)[:,None]
            cand_x=np.maximum(prevx+w, np.where(w_is2,NEG,prev+w))
            Kx[c][N]=np.max(cand_x,axis=0)
    # precompute u(nu,mu,d): for each vertex degree d, mu index g, nu index h
    for s in range(2,S+1):
        N=s-1
        upd(N)
        best=np.full(H,np.inf); bestn=np.full(H,np.inf)
        for c in range(1,min(C,N)+1):
            d=c+1
            # const[g,h] with u from nu_h
            nu=mu[None,:]; m_=mu[:,None]
            disc=1-4*m_*nu
            u=np.where(disc>=0,(1+np.sqrt(np.maximum(disc,0)))/(2*nu),np.nan)
            valid=(disc>=0)&(u>2*m_)&(u>0)
            const=np.log(u/d)+m_/u-F-nu*(u-d)
            const=np.where(valid,const,np.inf)
            tot=const+K[c][N][None,:]
            best=np.minimum(best,np.min(tot,axis=1)) if False else best  # placeholder
            # W_s(mu) <= max_c min_h (...)  -> compute per c the min over h, then max over c
            vc=np.min(np.where(K[c][N][None,:]>NEG/2,tot,np.inf),axis=1)
            # non-atom parent: c==1 requires child size >=3; c>=2 requires a part !=2
            if c==1:
                vcn=vc if N>=3 else np.full(H,-np.inf)
            else:
                totn=const+Kx[c][N][None,:]
                vcn=np.min(np.where(Kx[c][N][None,:]>NEG/2,totn,np.inf),axis=1)
            if c==1: Wa_s=vc; Wn_s=vcn
            else: Wa_s=np.maximum(Wa_s,vc); Wn_s=np.maximum(Wn_s,vcn)
        Wa[s]=np.where(np.isfinite(Wa_s),Wa_s,NEG); Wn[s]=np.where(np.isfinite(Wn_s),Wn_s,NEG)
    return Wa,Wn
if __name__=="__main__":
    S=int(sys.argv[1]); C=int(sys.argv[2]); H=int(sys.argv[3])
    grid=np.linspace(0.5/H,0.5,H)
    t=time.time(); Wa,Wn=bellman(S,C,grid); print("time",time.time()-t)
    pickle.dump((grid,Wa,Wn),open(f"bell_{S}_{C}_{H}.pkl","wb"))
    # compare with true envelope
    FA,FN=pickle.load(open(f"fr_{S}_{C if C<S else 0}.pkl","rb"))
    gaps=[];gapsn=[]
    for s in range(1,S+1):
        l,y=FA[s]; tru=np.max(l[:,None]+grid[None,:]*y[:,None],axis=0); gaps.append(np.max(Wa[s]-tru))
        if s in FN:
            l,y=FN[s]; trun=np.max(l[:,None]+grid[None,:]*y[:,None],axis=0); gapsn.append((np.max(Wn[s]-trun),s))
    print("max looseness W_all:",max(gaps),"min",min(gaps)," W_na:",max(gapsn))
