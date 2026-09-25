import numpy as np, weilwin as W
print(' x   | index(Q0 even) index(Q0 odd) | sigma+ = 2a.Q0e^-1.a (need <= -1) | sigma- = 2b.Q0o^-1.b (need <= 1) | full min e / o')
for x in [1.5,2,np.exp(0.8),3,4,5,7]:
    A=np.log(x)/2; N=int(170*A/np.pi)+30
    out=[]
    for par in (0,1):
        Q0,G,f=W.form_matrix('zeta',A,N,par,pole=False)
        Q,_,_=W.form_matrix('zeta',A,N,par,pole=True)
        d=1/np.sqrt(np.diag(G))
        e0=np.linalg.eigvalsh(Q0*d[:,None]*d[None,:]); e=np.linalg.eigvalsh(Q*d[:,None]*d[None,:])
        v=(W._F(0.5,f,A)+W._F(-0.5,f,A)) if par==0 else (W._S(0.5,f,A)-W._S(-0.5,f,A))
        sig=2*v@np.linalg.solve(Q0,v)
        out.append(((e0<0).sum(),sig,e[0]))
    print(f'{x:5.2f} | {out[0][0]} {out[1][0]} | {out[0][1]:+.9f} | {out[1][1]:+.6f} | {out[0][2]:+.2e} {out[1][2]:+.2e}')
