# Repro: the tail counts->single-degree EXCHANGE is DISSOLVED by the tangent-decouple.
# G(config) >= const(S0) + (d-1)*min_c phi_{S0}(c) =: B(S0);  some S0 in {(d-1)/3,(d-1)/4,(d-1)/5} gives B>=0
# for all d>=5 (tight=0 at the d=6 tie). 400k random mixed configs: worst G > 0.  (2026-09-03)
import math, random
random.seed(2)
F=math.log(621/64)/11; LOG32=math.log(3/2)
def rho(deg,y):
    if deg==1: return F
    if deg==2: return 2*F-LOG32+(y-1/3)/4
    if deg==3: return y/32
    if deg==4: return y/384
    return 0.0
def rng(deg): return [1.0] if deg==1 else [1/(2*deg-1),1/deg]
def minphi(sigma):
    return min(rho(deg,y)-sigma*y for deg in list(range(1,80))+[150,400] for y in rng(deg))
def B(d,S0):
    sigma=1/(d+S0); return F-math.log(1+S0/d)+S0/(d+S0)+(d-1)*minphi(sigma)
assert all(max(B(d,(d-1)/3),B(d,(d-1)/4),B(d,(d-1)/5))>=-1e-9 for d in range(5,2000)), "B>=0 fails"
worst=min(
    sum(rho(dg,y) for dg,y in kids)-(math.log(1+sum(y for _,y in kids)/d)-F)
    for _ in range(400000)
    for d in [random.randint(5,160)]
    for kids in [[(dg,1.0 if dg==1 else random.uniform(*rng(dg))) for dg in (random.choice([1,2,3,4,5,6,8,12]) for _ in range(d-1))]]
)
print(f"B(S0)>=0 for all d in [5,2000): OK;  worst G over 400k mixed configs = {worst:+.6f} (>=0 => dissolved)")
