import numpy as np, json, weilwin as W
from zetacycle2 import roots_of
dz=np.array(json.load(open('dh_zeros.json')))
for x in [40,57]:
    A=np.log(x)/2; N=int(170*A/np.pi)+30
    ev,V,f=W.min_eig('D',A,N,0)
    for j in (0,1):
        r=roots_of(V[:,j],f,A)
        e=[np.min(np.abs(r-g)) for g in dz[:10]]
        print(f'x={x} eigvec#{j} lam={ev[j]:+.2e} err first10:',' '.join(f'{v:.0e}' for v in e),flush=True)
    # odd sector count of negative eigenvalues
    evo,_,_=W.min_eig('D',A,N,1)
    print('   #neg even',(ev<-1e-12).sum(),'#neg odd',(evo<-1e-12).sum())
