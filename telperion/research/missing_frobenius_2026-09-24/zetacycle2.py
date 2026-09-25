import numpy as np, mpmath as mp, json, weilwin as W
zz=[float(mp.im(mp.zetazero(n))) for n in range(1,31)]
dz=json.load(open('dh_zeros.json'))
def roots_of(v,f,A,T=100):
    t=np.linspace(0.05,T,100000); F=W.Fhat(v,f,A,t,0)
    idx=np.where(np.sign(F[:-1])*np.sign(F[1:])<0)[0]
    out=[]
    for i in idx:
        a,b=t[i],t[i+1]; fa=W.Fhat(v,f,A,[a],0)[0]
        for _ in range(60):
            m=0.5*(a+b); fm=W.Fhat(v,f,A,[m],0)[0]
            if np.sign(fm)==np.sign(fa): a,fa=m,fm
            else: b=m
        out.append(0.5*(a+b))
    return np.array(out)
def run(kind,x,true,K=10):
    A=np.log(x)/2; N=int(170*A/np.pi)+30
    ev,V,f=W.min_eig(kind,A,N,0)
    r=roots_of(V[:,0],f,A)
    e=[np.min(np.abs(r-g)) for g in true[:K]]
    # how many consecutive true zeros are matched to within 1e-2
    good=0
    for g in true:
        if np.min(np.abs(r-g))<1e-2: good+=1
        else: break
    return ev[0],ev[1],e,good,r
if __name__=="__main__":
     for kind,x,true in [('zeta',2,zz),('zeta',2.5,zz),('zeta',3,zz),('zeta',3.5,zz),('zeta',4,zz),
                        ('D',5,dz),('D',8,dz),('D',11,dz),('D',13,dz),('D',15,dz),('D',17,dz),('D',40,dz),('D',57,dz)]:
        l0,l1,e,good,r=run(kind,x,true)
        print(f'{kind:4} x={x:5} lam0={l0:+.2e} lam1={l1:.2e}  #leading zeros matched<1e-2: {good:2d}  err1..10: '+' '.join(f'{v:.1e}' for v in e),flush=True)
        if kind=='D' and x>=40: print('   roots 84-88:',[round(v,4) for v in r if 84<v<88])
