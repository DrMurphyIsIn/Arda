# DH trap for the Bender-Brody-Muller construction.
# BBM: psi_z(x) = -zeta(z, x+1), Delta = 1 - e^{-ip}; Delta psi = x^{-z}; (xp+px) x^{-z} = i(2z-1) x^{-z};
# boundary psi(0)=0  <=> zeta(z)=0; eigenvalue E = i(2z-1) (real iff Re z = 1/2).
# General periodic a (mod 5):  phi_z(u) = -sum_{m>=1} a(m) (u+m)^{-z} = -A(e^{ip}) u^{-z},
# A(w) = (a1 w + a2 w^2 + a3 w^3 + a4 w^4 + a5 w^5)/(1 - w^5); phi_z(0) = -F_a(z).
# Check numerically: phi_z(u) = -5^{-z} sum_j a_j zeta(z, (u+j)/5) and phi_z(0) = -F_a(z) at D's off-line zero.
import mpmath as mp
mp.mp.dps=25
k=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
aD=[1,k,-k,-1,0]
z=mp.findroot(lambda s: mp.dirichlet(s,[0]+aD[:4]), mp.mpc(0.8085,85.6993))
print('D off-line zero z =',z)
phi0=-mp.power(5,-z)*sum(aD[j-1]*mp.zeta(z,mp.mpf(j)/5) for j in range(1,6))
print('phi_z(0) =',mp.nstr(phi0,5),'  (=> boundary condition satisfied)')
E=1j*(2*z-1); print('BBM-type eigenvalue E = i(2z-1) =',mp.nstr(E,10),' -> NOT real')
# check PT-relevant fact: coefficients real
print('D coefficients real:',all(mp.im(c)==0 for c in aD))
# check the zeta case embeds with a=(1,1,1,1,1)
z0=mp.zetazero(1); print('zeta embed check:', mp.nstr(mp.power(5,-z0)*sum(mp.zeta(z0,mp.mpf(j)/5) for j in range(1,6)),5))
