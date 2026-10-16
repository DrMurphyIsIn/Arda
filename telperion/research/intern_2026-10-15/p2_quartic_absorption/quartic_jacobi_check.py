# Check J(chi,chi) = -chi(-1)*pi for primary pi in Z[i] (quartic residue character),
# hence g(chi)^2 = J(chi,chi) g(chi^2) carries a -1 per prime (the Mobius sign).
import cmath
def primary(p):
    for a in range(-int(p**.5)-1,int(p**.5)+2):
        for b in range(-int(p**.5)-1,int(p**.5)+2):
            if a*a+b*b==p and b%2==0 and (a+b-1)%4==0:   # primary: a odd, b even, a+b = 1 mod 4
                return complex(a,b)
for p in [5,13,17,29,37,41,53]:
    pi=primary(p)
    a,b=int(pi.real),int(pi.imag)
    # i corresponds to t in F_p with a + b t = 0 mod p  (t^2=-1)
    t=(-a*pow(b,-1,p))%p
    assert (t*t+1)%p==0
    # quartic char: x^((p-1)/4) mod p, mapped to {1,i,-1,-i} via powers of t
    m={1:1,t:1j,p-1:-1,(p-t)%p:-1j}
    chi=lambda x: 0 if x%p==0 else m[pow(x,(p-1)//4,p)]
    J=sum(chi(x)*chi(1-x) for x in range(p))
    g=lambda c,k: sum((c(x)**k if c(x)!=0 else 0)*cmath.exp(2j*cmath.pi*x/p) for x in range(1,p))
    g1=g(chi,1); g2=g(chi,2)
    print(p, pi, "J=",complex(round(J.real),round(J.imag)), " -chi(-1)pi=", -chi(p-1)*pi,
          " |g1^2 - J*g2|=%.1e"%abs(g1*g1-J*g2), " g2/sqrt p=%.3f"%(g2.real/p**.5))
print("check mu(p)*gamma_{-1}(p) == conj(alpha(p))*gamma_1(p):")
for p in [5,13,17,29,37,41,53,61,73]:
    pi=primary(p); a,b=int(pi.real),int(pi.imag); t=(-a*pow(b,-1,p))%p
    m={1:1,t:1j,p-1:-1,(p-t)%p:-1j}
    chi=lambda x: 0 if x%p==0 else m[pow(x,(p-1)//4,p)]
    ga=lambda k: sum(chi(x)**k*cmath.exp(2j*cmath.pi*x/p) for x in range(1,p))/p**.5
    lhs=-ga(-1); rhs=(pi/abs(pi)).conjugate()*ga(1)
    print(p, "%.1e"%abs(lhs-rhs))
