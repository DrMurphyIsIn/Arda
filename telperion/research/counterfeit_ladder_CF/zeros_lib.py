import mpmath as mp
from cf_core import chi_m4, chi_5, chi_m20
C4=[chi_m4(n) for n in range(4)]; C5=[chi_5(n) for n in range(5)]; C20=[chi_m20(n) for n in range(20)]
def Efun(s):
    return (mp.zeta(s)*mp.dirichlet(s,C20) + mp.dirichlet(s,C4)*mp.dirichlet(s,C5))/2
def ZKfun(s):
    return mp.zeta(s)*mp.dirichlet(s,C20)
def L20(s):
    return mp.dirichlet(s,C20)
def thetaE(t):
    return mp.im(mp.loggamma(mp.mpc(0.5,t))) + t*mp.log(mp.sqrt(20)/(2*mp.pi))
def thetaL20(t):
    return mp.im(mp.loggamma(mp.mpc(0.75,t/2))) + (t/2)*mp.log(mp.mpf(20)/mp.pi)
def ZE(t):
    v = mp.exp(1j*thetaE(t))*Efun(mp.mpc(0.5,t)); return v
def ZL(t):
    v = mp.exp(1j*thetaL20(t))*L20(mp.mpc(0.5,t)); return v
