import numpy as np, json, weilwin as W
from zetacycle2 import roots_of
dz=np.array(json.load(open('dh_zeros.json')))
print('D on-line zeros 70-95:', np.round(dz[(dz>70)&(dz<95)],4))
for x in [20,25,28,30,32,34,40]:
    A=np.log(x)/2; N=int(170*A/np.pi)+30
    ev,V,f=W.min_eig('D',A,N,0)
    r=roots_of(V[:,0],f,A)
    w=r[(r>70)&(r<95)]
    desc=[]
    for v in w:
        d=np.min(np.abs(dz-v)); desc.append(f'{v:.4f}({d:.0e})')
    # height up to which all D zeros matched < 1e-6
    H=0
    for g in dz:
        if np.min(np.abs(r-g))<1e-6: H=g
        else: break
    print(f'x={x}: all D zeros matched to 1e-6 up to height {H:.2f}; cycle roots 70-95:',' '.join(desc),flush=True)
