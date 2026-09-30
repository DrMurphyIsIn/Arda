import numpy as np, json, weilwin as W
from zetacycle2 import roots_of
dz=np.array(json.load(open('dh_zeros.json')))
for x in [32,33,34,35,37,40,57,80,120]:
    A=np.log(x)/2; N=int(170*A/np.pi)+30
    ev,V,f=W.min_eig('D',A,N,0)
    r=roots_of(V[:,0],f,A)
    sh=r[np.argmin(np.abs(r-85.699348))]
    e=[np.min(np.abs(r-g)) for g in dz[:10]]
    print(f'x={x:4} lam0={ev[0]:+.3e} lam1={ev[1]:+.2e} shadow root={sh:.5f} (|.-85.69935|={abs(sh-85.699348):.1e}) median err first10={np.median(e):.1e}',flush=True)
