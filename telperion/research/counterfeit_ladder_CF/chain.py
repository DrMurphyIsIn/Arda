from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps=40
PHI=Fr(314159265358979323847,10**20); PLO=Fr(314159265358979323846,10**20)
Ahi = Fr(9,17)*PHI; Alo=Fr(9,17)*PLO
C2=Fr(16029,10000)
Lhi = Fr(2995732273553991,10**15) - 2*Fr(11447,10000)
Llo = Fr(299573227355399,10**14) - 2*Fr(11448,10000)
glo = Fr(5187377517639,10**12) - Fr(230756025842063,5*10**13)
ghi = Fr(58112,100000)
Hhi = Fr(3141331941,500000000); Hlo = Fr(6282663880299,10**12)
t14lo=Fr(6581939035062,10**12); t14hi=Fr(6581939035063,10**12)
t34lo=Fr(6549485735694,10**12); t34hi=Fr(6549485735695,10**12)
s14lo=Fr(52838100521,10**11); s14hi=Fr(528381005211,10**12)
s34lo=Fr(316402782326,10**12); s34hi=Fr(316402782327,10**12)
coshHi=Fr(136617,100000)
Em1lo=Fr(189532,10**6); Em3lo=Fr(6808,10**6)
S14sqlo=Fr(292668,10**6); S34sqlo=Fr(128462,10**6)
rhoP2hi=Fr(1170674,10**6); rhoP2lo=Fr(1170673,10**6)
Kp=Fr(54281,675); R=33; N=300
PElo=Fr(13498116,10**6); PKhi=Fr(-37393,100000)
X = C2*(Lhi-2*glo+2*Hhi+Fr(1,N)+Fr(3,20)+Fr(R*R,4*N*N)) - t14lo - t34lo
Y = 2*coshHi**2*rhoP2hi - 2*(s14lo+s34lo) - 2*(Em1lo*S14sqlo+Em3lo*S34sqlo) + Kp**2/(R*4*N*N) - PElo
print("X", float(X), "Y", float(Y), "E total", float((Ahi if X>0 else Alo)*X + Y))
X2 = C2*(Llo-2*ghi+2*Hlo-3) - t14hi - t34hi
Y2 = 2*1*rhoP2lo - 4*(s14hi+s34hi) - PKhi
print("X2", float(X2), "Y2", float(Y2), "K total", float((Alo if X2>0 else Ahi)*X2 + Y2))
