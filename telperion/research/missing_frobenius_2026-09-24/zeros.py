# Sign-change zero finder for real Z-functions on the critical line:
#  D  : Davenport-Heilbronn, coefficients mod 5 = (0,1,k,-k,-1), odd gamma factor
#  L5 : L(s,(./5)), coefficients (0,1,-1,-1,1), even gamma factor (same conductor, has Euler product)
import sys, json, time
import mpmath as mp
mp.mp.dps = 20
k = (mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
FUN = {
 'D':  ([0,1,k,-k,-1], mp.mpf(3)/4),
 'L5': ([0,1,-1,-1,1], mp.mpf(1)/4),
}
def theta(t, a0):  # phase making Lambda real on the line
    return mp.im(mp.loggamma(a0 + 1j*t/2)) + t/2*mp.log(5/mp.pi)
def Z(name, t):
    c, a0 = FUN[name]
    v = mp.exp(1j*theta(t,a0)) * mp.dirichlet(mp.mpf(0.5)+1j*t, c)
    return v
def run(name, T, h):
    zs=[]; t=mp.mpf(1.0); prev=Z(name,t); maxim=0
    while t < T:
        t2=t+h; cur=Z(name,t2)
        maxim=max(maxim, abs(mp.im(cur))/(abs(cur)+1e-30))
        if mp.re(prev)*mp.re(cur) < 0:
            r = mp.findroot(lambda x: mp.re(Z(name,x)), (t,t2), solver='anderson')
            zs.append(float(r))
        t,prev=t2,cur
    return zs, float(maxim)
if __name__=='__main__':
    name=sys.argv[1]; T=float(sys.argv[2]); h=float(sys.argv[3])
    t0=time.time(); zs,mi=run(name,T,h)
    json.dump({'name':name,'T':T,'h':h,'zeros':zs,'max_rel_imag':mi}, open(f'zeros_{name}_{int(T)}.json','w'))
    print(name, len(zs), 'zeros; max rel imag', mi, 'time', time.time()-t0)
