import mpmath as mp, time, sys, json
from zeros_lib import *
mp.mp.dps=20
T = float(sys.argv[1]) if len(sys.argv)>1 else 150
which = sys.argv[2] if len(sys.argv)>2 else 'E'
F = Efun if which=='E' else L20
Zf = ZE if which=='E' else ZL
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
t0=time.time()
# on-line zeros via sign changes
step=0.02
ts=[0.1+step*i for i in range(int((T-0.1)/step)+1)]
vals=[mp.re(Zf(t)) for t in ts]
online=[]
for i in range(len(ts)-1):
    if vals[i]==0 or vals[i]*vals[i+1]<0:
        r = mp.findroot(lambda t: mp.re(Zf(t)), (ts[i],ts[i+1]), solver='anderson')
        online.append(r)
print("online count", len(online), "time", time.time()-t0, flush=True)
# boxes
boxes=[]
edges=list(range(0, int(T)+1, 10))
if edges[-1] < T: edges.append(T)
if which=='E':
    sl, sr = -2.0, 3.0
else:
    sl, sr = -2.0, 3.0
offline=[]
tot_ap=0
for ta,tb in zip(edges, edges[1:]):
    ta_=max(ta,0.1)
    pts=[mp.mpc(sr,ta_), mp.mpc(sr,tb), mp.mpc(sl,tb), mp.mpc(sl,ta_), mp.mpc(sr,ta_)]
    # densify edges
    dense=[]
    for a,b in zip(pts,pts[1:]):
        n=int(abs(b-a)/0.25)+1
        dense += [a+(b-a)*j/n for j in range(n)]
    dense.append(pts[-1])
    w = winding(F, dense)
    non = sum(1 for z in online if ta_<z<=tb)
    tot_ap += int(mp.nint(w))
    print(f"box t in [{ta_},{tb}]: argument-principle count {mp.nstr(w,6)}, on-line {non}", flush=True)
    if int(mp.nint(w)) != non:
        # search off-line zeros in this box
        found=[]
        for s0 in [0.55,0.65,0.75,0.85,0.95,1.05,1.2,1.4]:
            for tt in [ta_+0.5*j for j in range(int((tb-ta_)/0.5)+1)]:
                try:
                    r=mp.findroot(F, mp.mpc(s0,tt))
                except Exception:
                    continue
                if abs(F(r))<1e-12 and ta_<mp.im(r)<=tb and mp.re(r)>0.5+1e-8:
                    if all(abs(r-x)>1e-8 for x in found):
                        found.append(r)
        print("   off-line (Re>1/2) found:", [mp.nstr(z,12) for z in found], flush=True)
        offline += found
print("total AP", tot_ap, "online", len(online), "offline pairs", len(offline), "(each gives 2 zeros: rho, 1-conj rho)")
json.dump({'online':[str(z) for z in online], 'offline':[[str(mp.re(z)),str(mp.im(z))] for z in offline]}, open(f'zeros_{which}_{int(T)}.json','w'))
print("time", time.time()-t0)
