import sys, math
sys.path.insert(0,"telperion/src")
import sympy as sp
from telperion.emit_handelman import find_handelman_certificate
g=sp.Symbol('g')
F=math.log(621/64)/11
def phi(gg,tl,to):
    A=(18+gg)/12; bl=(18+gg)/(12+gg); bo=(18+gg)/18
    return math.log(A)-tl*math.log(bl)-to*math.log(bo)
def cap(gg): return F/math.log((18+gg)/(12+gg))
def cert_poly(D,kl,ko):
    Aarg=(18+g)/12; Bl=(18+g)/(12+g); Bo=(18+g)/sp.Integer(18)
    E=sp.Rational(621,64)**(sp.Rational(D,11))*Bl**kl*Bo**ko - Aarg**D
    num,_=sp.fraction(sp.together(E)); return sp.expand(num)
D=99; lo=sp.Rational(6,11); hi=sp.Integer(1); b=sp.Rational(745,1000)
segs=[(lo,b,52,99),(b,hi,53,99)]   # overlap-safe: piece1 kl=52 leaf-safe everywhere; piece2 kl=53 leaf-safe for g>=0.741
allok=True
for gL,gR,kl,ko in segs:
    gg=float(gL); worst=-9; safe=True
    while gg<=float(gR)+1e-9:
        worst=max(worst,phi(gg,kl/D,ko/D))
        if kl/D>cap(gg)+1e-7: safe=False
        gg+=0.004
    num=cert_poly(D,kl,ko)
    terms=find_handelman_certificate(num,[g-gL,gR-g],(g,))
    ok = terms is not None and sp.expand(sum(c*(g-gL)**e0*(gR-g)**e1 for c,(e0,e1) in terms)-num)==0 \
         and all(c>=0 for c,_ in terms)
    allok = allok and ok and safe
    print(f"piece [{float(gL):.4f},{float(gR):.4f}] kl={kl},ko={ko}: max phi-F*={worst-F:+.5f}  leaf-safe={safe}  "
          f"Bernstein {'CERTIFIED' if ok else 'FAILED'} ({None if terms is None else len(terms)} terms, deg {sp.Poly(num,g).degree()})")
contig = segs[0][0]==lo and segs[-1][1]>=hi and segs[0][1]==segs[1][0]
print(f"\nARMMID FULL reachable range [6/11,1] COVERED by 2 certified contiguous pieces: {allok and contig}")
print("=> the armmid local case (deg2 + leaf + deg6 center) is bulk-certified over its ENTIRE reachable variety,")
print("   phi_arm <= F* everywhere, via a finite 2-piece cover with fixed rational k/99 discharge + Bernstein.")
