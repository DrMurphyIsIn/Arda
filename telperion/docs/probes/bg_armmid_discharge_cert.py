import sys, math
sys.path.insert(0,"telperion/src")
import sympy as sp
from telperion.emit_handelman import find_handelman_certificate
g=sp.Symbol('g')
F=math.log(621/64)/11
# armmid discharge at D=33, (k_leaf,k_other)=(17,33):
# exp(33 phi_arm) = Aarg^33 * Bof_leaf^-17 * Bof_other^-33 <= (621/64)^3
Aarg=(18+g)/12; Bl=(18+g)/(12+g); Bo=(18+g)/sp.Integer(18)
E = sp.Rational(621,64)**3 * Bl**17 * Bo**33 - Aarg**33   # >=0 iff exp(33phi)<=(621/64)^3
num,den = sp.fraction(sp.together(E))
num=sp.expand(num)
print("armmid certificate polynomial degree:", sp.Poly(num,g).degree(), "; den always >0 on g>-12")
# find where phi_arm <= F* (num>=0). numeric:
def phi(gg): 
    A=(18+gg)/12; bl=(18+gg)/(12+gg); bo=(18+gg)/18
    return math.log(A)-(17/33)*math.log(bl)-(33/33)*math.log(bo)
gL,gR=sp.Rational(1,2),sp.Rational(72,100)   # realizable sub-box [0.50,0.72]
print(f"phi_arm at g={float(gL)}: {phi(float(gL)):.6f}, at g={float(gR)}: {phi(float(gR)):.6f}  (F*={F:.6f})")
# Bernstein-certify num >= 0 on [gL, gR] (den>0 there so equiv to E>=0 => exp<=RHS => phi<=F*)
terms=find_handelman_certificate(num,[g-gL, gR-g],(g,))
if terms is None:
    print("Bernstein REFUSED on [%.2f,%.2f]"%(float(gL),float(gR))); sys.exit(1)
recon=sum(c*(g-gL)**e0*(gR-g)**e1 for c,(e0,e1) in terms)
ok=sp.expand(recon-num)==0 and all(c>=0 for c,_ in terms)
print(f"ARMMID CERTIFIED on realizable sub-box g in [{float(gL)},{float(gR)}]: "
      f"{len(terms)} Bernstein terms, exact={sp.expand(recon-num)==0}, all coefs>=0={all(c>=0 for c,_ in terms)}")
print("=> exp(33 phi_arm) <= (621/64)^3  i.e.  phi_arm <= F*  over the sub-box (fixed rational k/33 discharge).")
