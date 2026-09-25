import sys, math, pickle, time
import numpy as np
from rootb import PHI
from bellman import bellman
NEG=-1e30
def knapH(Wa,Wn,k,N):
    """vectorized over grid columns: Wa,Wn (S+1,H). returns (N+1,H) best with >=1 na part, k parts."""
    S=Wa.shape[0]-1; H=Wa.shape[1]
    A=np.full((N+1,H),NEG); A[0]=0; Bn=np.full((N+1,H),NEG)
    for i in range(k):
        A2=np.full((N+1,H),NEG); B2=np.full((N+1,H),NEG)
        for s in range(1,min(S,N)+1):
            A2[s:]=np.maximum(A2[s:],A[:N+1-s]+Wa[s]); B2[s:]=np.maximum(B2[s:],Bn[:N+1-s]+Wa[s])
            B2[s:]=np.maximum(B2[s:],A[:N+1-s]+Wn[s])
        A,Bn=A2,B2
    return Bn
if __name__=="__main__":
  S=int(sys.argv[1]); H=int(sys.argv[2]); Nmax=int(sys.argv[3])
  grid=np.linspace(0.5/H,0.5,H)
  thr={2:28,3:70,4:104,5:298}   # own low-degree Lean thresholds on n-1 (k>=6: 491 uniform-ish; use 491)
  t0=time.time()
  tabs={C:bellman(S,C,grid) for C in list(range(1,23))+[S]}
  print("bellman tables",time.time()-t0,flush=True)
  worst={}
  for k in range(2,Nmax):
      if k>=24: Nk=min(Nmax,90)    # k>=24 and n>=91 is the proven high-degree theorem
      else: Nk=min(Nmax, thr.get(k,491))
      if Nk<k+1: continue
      Wa,Wn=tabs[k-1] if k<=23 else tabs[S]
      Bn=knapH(Wa,Wn,k,Nk-1)
      t=1/(k*grid)
      val=np.log(t)+1/t-1+Bn
      best=np.min(val,axis=1)
      for n in range(k+1,Nk+1):
          m=PHI[n]-best[n-1]
          if n not in worst or m<worst[n][0]: worst[n]=(m,k)
      print("k",k,"done",time.time()-t0,flush=True)
  bad=sorted((n,round(m,6),k) for n,(m,k) in worst.items() if m<=0)
  print("H",H,"failures:",bad[:50],"count",len(bad))
  mins=sorted((m,n,k) for n,(m,k) in worst.items() if n>=10)[:10]
  print("smallest margins n>=10:",[(round(m,6),n,k) for m,n,k in mins])
  pickle.dump(worst,open(f"worstbell2_{S}_{H}_{Nmax}.pkl","wb"))
