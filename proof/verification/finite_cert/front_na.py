"""Per-size Pareto frontiers (logT, y) of planted branches, all and non-atom, with a child-count cap.
Non-atom status depends only on the child-size multiset: some child of size >= 3, or a leaf child with k >= 2."""
import sys, math, time, pickle
import numpy as np
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..'))
import bg_spider_reduction as B
F=B.F
def run(S, KC):
    """KC = max children per vertex (None = no cap)."""
    KC = KC or S
    st=B._Store(); states={(0,0,0,0):st.add(np.array([0.0]),np.array([0.0]))}
    FA={};FN={}
    for m in range(1,S+1):
        cl=[];cy=[];nl=[];ny=[]
        for (k,s,big,lf),e in states.items():
            if s!=m-1 or k>KC: continue
            d=k+1;R=st.R[e]; l=st.lp[e]+np.log((d+R)/d); y=1/(d+R)
            cl.append(l);cy.append(y)
            if big or (lf and k>=2): nl.append(l);ny.append(y)
        cl,cy=np.concatenate(cl),np.concatenate(cy)
        kp=B._prune_front(cl,cy); FA[m]=(cl[kp]-m*F,cy[kp])
        if nl:
            nl,ny=np.concatenate(nl),np.concatenate(ny); kp2=B._prune_front(nl,ny); FN[m]=(nl[kp2]-m*F,ny[kp2])
        if m==S: break
        Il,Iy=cl[kp],cy[kp]
        for s in range(0,S-m):
            for k in range(0,KC):
                for big in (0,1):
                    for lf in (0,1):
                        src=states.get((k,s,big,lf))
                        if src is None: continue
                        lp=(st.lp[src][:,None]+Il[None,:]).ravel(); R=(st.R[src][:,None]+Iy[None,:]).ravel()
                        key=(k+1,s+m,max(big,int(m>=3)),max(lf,int(m==1))); old=states.get(key)
                        if old is not None: alp,aR=np.concatenate((st.lp[old],lp)),np.concatenate((st.R[old],R))
                        else: alp,aR=lp,R
                        kp3=B._prune_state(alp,aR,k+1); no=0 if old is None else len(old)
                        keep_old=old[kp3[kp3<no]] if old is not None else np.empty(0,dtype=np.int64)
                        kn=kp3[kp3>=no]-no
                        newidx=st.add(lp[kn],R[kn]) if len(kn) else np.empty(0,dtype=np.int64)
                        states[key]=np.concatenate((keep_old,newidx))
    return FA,FN
if __name__=="__main__":
    S=int(sys.argv[1]); KC=int(sys.argv[2]) if sys.argv[2]!="0" else None
    t=time.time(); FA,FN=run(S,KC)
    pickle.dump((FA,FN),open(f"fr_{S}_{sys.argv[2]}.pkl","wb")); print(S,KC,"done",time.time()-t,flush=True)
