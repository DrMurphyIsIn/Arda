import numpy as np, weilwin as W
xs=[2.0,np.exp(0.8),3.0,4.0,5.0,7.0,11.0,17.0,25.0,28.0,30.0,31.0,32.0,35.0,40.0]
print('x     A    | zeta(e,o)            | D(e,o)               | Lchi(e,o)            | arch+pole(e,o)')
for x in xs:
    A=np.log(x)/2
    row=[]
    for kind in ('zeta','D','Lchi','arch'):
        for par in (0,1):
            N=int(max(40, 14*A*6))
            ev,_,_=W.min_eig(kind,A,N,par)
            row.append(ev[0])
    print(f'{x:6.2f} {A:.3f} | '+' | '.join(f'{row[2*i]:+.3e} {row[2*i+1]:+.3e}' for i in range(4)),flush=True)
