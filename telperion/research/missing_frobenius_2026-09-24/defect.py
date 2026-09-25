import numpy as np, weilwin as W
x=40; A=np.log(x)/2; N=int(170*A/np.pi)+30
ev,V,f=W.min_eig('D',A,N,0); v=V[:,0]
cD=W.weights('D',40); cL=W.weights('Lchi',40)
QL,G,_=W.form_matrix('Lchi',A,N,0); QD,_,_=W.form_matrix('D',A,N,0)
nv=v@G@v
print('Q_D(xi)/|xi|^2=',v@QD@v/nv,' Q_Lchi(xi)/|xi|^2=',v@QL@v/nv, ' (same arch part)')
rows=[]
for n in range(2,40):
    hn=W.corr(A,f,np.array([np.log(n)]),0)[:,:,0]; hn=0.5*(hn+hn.T)
    hx=v@hn@v/nv
    dD=-2*cD[n]/np.sqrt(n)*hx; dL=-2*cL[n]/np.sqrt(n)*hx
    rows.append((n,cD[n],cL[n],hx,dD,dL,dD-dL))
rows.sort(key=lambda r:r[6])
print(' n   c_D(n)   ReChi*Lam   h_xi(log n)   contrib_D   contrib_L   D-L')
for r in rows[:10]: print(f'{r[0]:3d} {r[1]:+8.4f} {r[2]:+8.4f} {r[3]:+10.4f} {r[4]:+10.4f} {r[5]:+10.4f} {r[6]:+9.4f}')
print('sum D-L over all n:',sum(r[6] for r in rows))
# which n are prime powers?
