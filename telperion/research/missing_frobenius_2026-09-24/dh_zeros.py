import mpmath as mp, numpy as np, json
mp.mp.dps=20
k=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
def D(s): return 5**(-s)*(mp.zeta(s,mp.mpf(1)/5)+k*mp.zeta(s,mp.mpf(2)/5)-k*mp.zeta(s,mp.mpf(3)/5)-mp.zeta(s,mp.mpf(4)/5))
def Z(t):
    s=mp.mpf(0.5)+1j*t
    v=(5/mp.pi)**(s/2)*mp.gamma((s+1)/2)*D(s)
    return v
# check reality
print('imag/real check', Z(10.3), Z(40.1))
ts=np.arange(0.2,100.0,0.02); vals=[float(mp.re(Z(t))) for t in ts]
zs=[]
for i in range(len(ts)-1):
    if vals[i]==0 or vals[i]*vals[i+1]<0:
        r=mp.findroot(lambda t: mp.re(Z(t)),(ts[i],ts[i+1]),solver='anderson')
        zs.append(float(r))
print(len(zs),'zeros on line below 100'); print(zs[:12])
# off-line zero
r=mp.findroot(D,mp.mpc(0.8085,85.6993)); print('offline',r)
json.dump(zs,open('dh_zeros.json','w'))
