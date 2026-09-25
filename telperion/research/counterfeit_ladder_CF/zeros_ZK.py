# zeros of zeta_K = zeta * L(chi_-20) up to T: zeta zeros from mpmath.zetazero, L zeros by sign changes of
# the Hardy function ZL, with an argument-principle count of L(s, chi_-20) per box as completeness check.
import mpmath as mp, json, sys, time
from zeros_lib import ZL, L20
mp.mp.dps = 20
T = float(sys.argv[1])
t0=time.time()
zz=[]; n=1
while True:
    z = mp.zetazero(n)
    if mp.im(z) > T: break
    zz.append(mp.im(z)); n+=1
print("zeta zeros", len(zz), time.time()-t0, flush=True)
step=0.02
ts=[0.05+step*i for i in range(int((T-0.05)/step)+1)]
vals=[mp.re(ZL(t)) for t in ts]
lz=[]
for i in range(len(ts)-1):
    if vals[i]*vals[i+1]<0:
        lz.append(mp.findroot(lambda t: mp.re(ZL(t)), (ts[i],ts[i+1]), solver='anderson'))
print("L20 zeros (sign changes)", len(lz), time.time()-t0, flush=True)
def winding(f, pts):
    tot = mp.mpf(0)
    for a,b in zip(pts, pts[1:]):
        stack=[(a,b,f(a),f(b))]
        while stack:
            p,q,fp,fq = stack.pop()
            d = mp.im(mp.log(fq/fp))
            if abs(d) > 0.5 and abs(q-p) > 1e-9:
                m=(p+q)/2; fm=f(m)
                stack.append((m,q,fm,fq)); stack.append((p,m,fp,fm))
            else:
                tot += d
    return tot/(2*mp.pi)
# argument principle for L20 on [-1.5, 2.5] x [0.05, T] in boxes of 20
edges=list(range(0,int(T)+1,20))
if edges[-1]<T: edges.append(T)
tot=0
for ta,tb in zip(edges,edges[1:]):
    ta_=max(ta,0.05)
    pts=[mp.mpc(2.5,ta_), mp.mpc(2.5,tb), mp.mpc(-1.5,tb), mp.mpc(-1.5,ta_), mp.mpc(2.5,ta_)]
    dense=[]
    for a,b in zip(pts,pts[1:]):
        nn=int(abs(b-a)/0.25)+1
        dense += [a+(b-a)*j/nn for j in range(nn)]
    dense.append(pts[-1])
    w=winding(L20, dense)
    non=sum(1 for z in lz if ta_<z<=tb)
    print(f"L20 box [{ta_},{tb}]: AP {mp.nstr(w,6)} sign-changes {non}", flush=True)
json.dump({'zeta':[str(x) for x in zz], 'L20':[str(x) for x in lz]}, open(f'zeros_ZK_{int(T)}.json','w'))
print("done", time.time()-t0)
