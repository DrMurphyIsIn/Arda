from wf import *
import sys, time
NM = 40
def reps(form, nmax):
    a = np.zeros(nmax+1); r = int(np.sqrt(nmax))+3
    for x in range(-r, r+1):
        for y in range(-r, r+1):
            n = form(x, y)
            if 1 <= n <= nmax: a[n] += 1
    return a/2
a1 = reps(lambda x,y: x*x+5*y*y, NM); a2 = reps(lambda x,y: 2*x*x+2*x*y+3*y*y, NM)
aK = a1 + a2; aL = a1 - a2
aL[1] = 1; assert aK[1] == 1 and a1[1] == 1
cE = vonmangoldt_coeffs(a1, NM); cK = vonmangoldt_coeffs(aK, NM); cL = vonmangoldt_coeffs(aL, NM)
C = lambda c: [(n, float(c[n])) for n in range(2, NM+1) if abs(c[n]) > 1e-25]
if __name__ == '__main__':
    print('cE', [(n, round(float(cE[n]),4)) for n in range(2,40) if abs(cE[n])>1e-20])
    cross = [cE[n] - (cK[n]+cL[n])/2 for n in range(NM+1)]
    print('cross', [(n, round(float(cross[n]),4)) for n in range(2,40) if abs(cross[n])>1e-20])
    Ns = [int(v) for v in sys.argv[1].split(',')]; xs = [float(v) for v in sys.argv[2].split(',')]
    for x in xs:
        t=time.time()
        rE = [lam(x, N, GAM['ZK'], C(cE)) for N in Ns]
        rK = lam(x, Ns[-1], GAM['ZK'], C(cK))
        print('x=%.2f E(N=%s)=%s  zK=%+.3e (%.0fs)' % (x, Ns, ['%+.3e'%v for v in rE], rK, time.time()-t), flush=True)
