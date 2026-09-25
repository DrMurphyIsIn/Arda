import numpy as np, mpmath as mp, json, weilwin as W
zz=[float(mp.im(mp.zetazero(n))) for n in range(1,31)]
dz=json.load(open('dh_zeros.json'))
def cyc_zeros(kind,A,N):
    ev,V,f=W.min_eig(kind,A,N,0)
    v=V[:,0]
    t=np.linspace(0.05,100,200000); F=W.Fhat(v,f,A,t,0)
    idx=np.where(np.sign(F[:-1])*np.sign(F[1:])<0)[0]
    roots=[]
    for i in idx:  # secant refine
        a,b=t[i],t[i+1]
        for _ in range(40):
            fa,fb=W.Fhat(v,f,A,[a,b],0)
            c=b-fb*(b-a)/(fb-fa); 
            if abs(c-b)<1e-15: break
            a,b=b,c
        roots.append(b)
    return ev[:2],np.array(roots)
def err(roots,true,K):
    out=[]
    for g in true[:K]:
        out.append(np.min(np.abs(roots-g)) if len(roots) else np.nan)
    return np.array(out)
for x in [3,5,8,11,13,17,25,31,35,40,57]:
    A=np.log(x)/2; N=int(170*A/np.pi)+30
    for kind,true in (('zeta',zz),('D',dz)):
        ev,r=cyc_zeros(kind,A,N)
        e=err(r,true,8)
        nb=np.sum(r<80); 
        near=r[(r>80)&(r<92)]
        print(f'x={x:3} {kind:4} lam0={ev[0]:+.2e} lam1={ev[1]:.2e} #roots<80={nb:3d} (true {sum(np.array(true)<80)}) '
              f'err[1..8]=' + ' '.join(f'{v:.0e}' for v in e) + '  roots80-92=' + ' '.join(f'{v:.3f}' for v in near),flush=True)
print('DH true zeros 80-92:', [round(z,3) for z in dz if 80<z<92], ' offline 85.699 +- 0.3085i')
print('zeta true 80-92:', [round(float(mp.im(mp.zetazero(n))),3) for n in range(20,32) if 80<float(mp.im(mp.zetazero(n)))<92])
