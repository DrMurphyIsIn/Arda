import json, math, sys
import numpy as np
import mpmath as mp
T=int(sys.argv[1]) if len(sys.argv)>1 else 1200
A0={'D':0.75,'L5':0.25}
def theta(t,a0): return float(mp.im(mp.loggamma(a0+1j*t/2)) + t/2*math.log(5/math.pi))
def gue(s): return 32/math.pi**2*s*s*math.exp(-4*s*s/math.pi)
def goe(s): return math.pi/2*s*math.exp(-math.pi*s*s/4)
def cdf(f,x,n=400):
    xs=np.linspace(0,x,n); return np.trapezoid([f(v) for v in xs],xs)
out={}
for name in ['D','L5']:
    z=np.array(json.load(open(f'zeros_{name}_{T}.json'))['zeros'])
    a0=A0[name]
    th=np.array([theta(g,a0) for g in z])
    # counting residual: n - theta/pi at each zero (midpoint convention n-1/2)
    resid=np.arange(1,len(z)+1)-0.5 - th/math.pi
    # detect steps: moving average of residual over windows
    rep={'n':len(z)}
    for H in [80,86,100,114,120,166,177,200,400,600,800,1000,1190]:
        m=(z<H)&(z>H-40)
        rep[f'mean_resid_[{H-40},{H}]']=round(float(resid[m].mean()),3) if m.any() else None
    # spacing stats, unfolded by theta/pi, locally renormalised to mean 1 in blocks of 200
    x=th/math.pi; s=np.diff(x)
    sn=np.concatenate([b/b.mean() for b in np.array_split(s, max(1,len(s)//200))])
    rep['mean_spacing_raw']=float(s.mean())
    for c in [0.1,0.25,0.5]:
        rep[f'P(s<{c})']=round(float((sn<c).mean()),4)
        rep[f'GUE P(s<{c})']=round(float(cdf(gue,c)),4); rep[f'GOE P(s<{c})']=round(float(cdf(goe,c)),4)
    # KS vs GUE and GOE
    ss=np.sort(sn); emp=np.arange(1,len(ss)+1)/len(ss)
    grid=np.linspace(0,4,801); G=np.cumsum([gue(v) for v in grid])*(grid[1]-grid[0]); O=np.cumsum([goe(v) for v in grid])*(grid[1]-grid[0])
    rep['KS_GUE']=round(float(np.max(np.abs(emp-np.interp(ss,grid,G)))),4)
    rep['KS_GOE']=round(float(np.max(np.abs(emp-np.interp(ss,grid,O)))),4)
    rep['P(s>2)']=round(float((sn>2).mean()),4); rep['GUE P(s>2)']=round(1-float(cdf(gue,2)),4); rep['GOE P(s>2)']=round(1-float(cdf(goe,2)),4)
    rep['var_s']=round(float(sn.var()),4)
    rep['min_s']=round(float(sn.min()),4)
    out[name]=rep
print(json.dumps(out,indent=1))
json.dump(out,open(f'analysis_{T}.json','w'),indent=1)
