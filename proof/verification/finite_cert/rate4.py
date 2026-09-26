"""Per-cap rates with cap-refined message ranges: in a cap-D tree every branch has y >= ymin = 1/(2D-1)."""
exec(open(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)),"rate.py")).read().split("lo,hi=0.0,0.002")[0])
import pickle
def classes(D):
    ym=1/(2*D-1)
    out=[]
    # non-atom deg-2 (bcc1): child non-leaf, y_c in [ym,1/2]
    if D>=2: out.append((1,1/(2+0.5),1/(2+ym)))
    for j in (2,3):
        if D-1>=j: out.append((j,1/(j+1+j),1/(j+1+j*ym)))
    if D-1>=4: out.append((4,1/(2*(D-1)+1),1/(5+4*ym)))   # bcc>=4: y in [1/(2c+1), 1/(c+1+c*ym)] with c>=4 -> max at c=4
    return out
def child_types_cap(alpha,D):
    T=[]
    for nm,b,y,bcc,s in AT:
        if bcc>D-1: continue
        beta=-(b+rho(bcc,y)); T.append((nm,y,rho(bcc,y)+beta-alpha*s, nm=="C"))
    for (bcc,lo,hi) in classes(D):
        for y in (lo,hi): T.append((f"N{bcc}",y,rho(bcc,y),False))
    return T
def d2(alpha,T):
    m=1e9
    for nm,y,w,isC in T:
        if nm in ("L","C"): continue
        rv=A+(1/(2+y)-1/3)/4
        m=min(m, w-math.log(1+y/2)+F-rv-alpha)
    return m
def alpha_cap(D):
    lo,hi=0.0,0.05
    for it in range(40):
        a=(lo+hi)/2; T=child_types_cap(a,D)
        ok=d2(a,T)>=0 and all(minval(d,a,T)>=0 for d in range(3,D+1))
        if ok: lo=a
        else: hi=a
    return lo
L=math.log(26/23)
sp=pickle.load(open("spider_cache_520.pkl","rb"))
phisp={n:math.log(v[0])-(n-1)*F for n,v in sp.items()}
res={}
for k in range(2,24):
    al=alpha_cap(k)*0.95; T=child_types_cap(al,k)
    vals=[(y,w-0*0) for nm,y,w,isC in T]   # w already = rateG-type value for atoms (rho+beta-alpha s) ... convert
    # root per-child value: rateG + mu*y ; atoms: bell+alpha s = -(rho+beta)+... recompute
    vals=[]
    for nm,b,y,bcc,s in AT:
        if bcc>k-1: continue
        vals.append((y,b+al*s))
    for (bcc,lo,hi) in classes(k):
        for y in (lo,hi): vals.append((y,-rho(bcc,y)))
    best=min(math.log(t)+1/t-1+k*max(w+y/(k*t) for y,w in vals) for t in np.linspace(1.001,6,4000))
    need=[n for n in range(4,521) if -al*(n-1)+best>=phisp[n]]
    res[k]=(al,best,max(need) if need else 3)
    print(f"k={k:2d} alpha_k={al:.6f} R_k={best:.4f} last n<=520 not excluded={res[k][2]}  floor-based N={1+(best-(L-1/96))/al:.0f}",flush=True)
print("N1 =",max(r[2] for r in res.values())+1)
