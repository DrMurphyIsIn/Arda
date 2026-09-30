from sk import *
import sk
# deficit: (1/k) log( sum_n |c(n)| n^-1/2 |g_k(+-log n)| / s_k ) for zeta, base 5, test (0.3,2,16.568)
te=Tst(5.,.3,2,16.568); K=6; N=int(5.**K)+1
c=coeffs_from_a(a_of('zeta',N)); ns=np.nonzero(c>1e-14)[0]; ns=ns[ns>=2]
s=arith('zeta',te,K)
Nf=1<<21; dt=0.004; t=te.g0+(np.arange(Nf)-Nf//2)*dt; Ft2=np.abs(te.F(.5+1j*t))**2
du=2*np.pi/(Nf*dt); u=(np.arange(Nf)-Nf//2)*du
for k in range(1,K+1):
    G=np.fft.fftshift(np.fft.fft(np.fft.ifftshift(Ft2**k)))*dt/(2*np.pi)*np.exp(-1j*te.g0*u)
    lg=np.log(ns); gv=np.interp(lg,u,G.real)+1j*np.interp(lg,u,G.imag)
    tb=np.sum(c[ns]/np.sqrt(ns)*2*np.abs(gv))
    print(k, f's_k={s[k-1]:.4g} trivial={tb:.4g} deficit/k={np.log(tb/s[k-1])/k:.3f}')
