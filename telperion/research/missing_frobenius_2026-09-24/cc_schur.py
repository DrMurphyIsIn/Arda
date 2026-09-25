import numpy as np, weilwin as W
def constrained_min(Q,G,C):
    # min Rayleigh on {v: C v = 0}
    U,s,Vt=np.linalg.svd(C); P=Vt[C.shape[0]:].T
    Qp=P.T@Q@P; Gp=P.T@G@P
    L=np.linalg.cholesky(Gp); Li=np.linalg.inv(L)
    return np.linalg.eigvalsh(Li@Qp@Li.T)[0]
print('x    | full(e)   full(o)  | polefree(e: a.v=0) polefree(e: a.v=0,v0=0) polefree(o: b.v=0) | neg(Q0e) neg(Q0o) sigma+ sigma- ')
for x in [1.5,2.0,2.2,2.5,3.0,3.27,3.3,3.5]:
    A=np.log(x)/2; N=48
    out=[]
    for par in (0,1):
        Q,G,f=W.form_matrix('arch',A,N,par,pole=True)
        Q0,_,_=W.form_matrix('arch',A,N,par,pole=False)
        d=1/np.sqrt(np.diag(G))
        full=np.linalg.eigvalsh(Q*d[:,None]*d[None,:])[0]
        if par==0:
            v=W._F(0.5,f,A)+W._F(-0.5,f,A)
            pf=constrained_min(Q0,G,v[None,:])
            e0=np.zeros(N); e0[0]=1
            pf2=constrained_min(Q0,G,np.vstack([v,e0]))
            sig=2*v@np.linalg.solve(Q0,v)
            neg=(np.linalg.eigvalsh(Q0*d[:,None]*d[None,:])<0).sum()
            out+= [full,pf,pf2,neg,sig]
        else:
            v=W._S(0.5,f,A)-W._S(-0.5,f,A)
            pf=constrained_min(Q0,G,v[None,:])
            sig=2*v@np.linalg.solve(Q0,v)
            neg=(np.linalg.eigvalsh(Q0*d[:,None]*d[None,:])<0).sum()
            out+= [full,pf,neg,sig]
    fe,pfe,pfe2,nege,sp,fo,pfo,nego,sm=out
    print(f'{x:5.2f} | {fe:+.4e} {fo:+.4e} | {pfe:+.4f} {pfe2:+.4f} {pfo:+.4f} | {nege} {nego} {sp:+.5f} {sm:+.6f}')
