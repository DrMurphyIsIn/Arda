import sympy as sp
h=sp.Symbol('h')
Q = sp.expand(621*3**7 - 64*(3+h)**7)   # 64*3^7*(621/64 - (1+h/3)^7), >=0 on [0,1]
a=sp.Poly(Q,h).all_coeffs()[::-1]       # a[k] = coeff of h^k
degQ=sp.Poly(Q,h).degree()
def bernstein_coeffs(n):
    # Q = sum_i b_i * C(n,i) h^i (1-h)^{n-i}; b_i = sum_{k=0}^i [C(i,k)/C(n,k)] a[k]
    b=[]
    for i in range(n+1):
        bi=sp.Integer(0)
        for k in range(0,min(i,degQ)+1):
            bi+= sp.binomial(i,k)/sp.binomial(n,k)*a[k]
        b.append(sp.nsimplify(bi))
    return b
for n in (7,8,10,12,14):
    b=bernstein_coeffs(n)
    allpos=all(bi>=0 for bi in b)
    # exact check: Q == sum b_i C(n,i) h^i (1-h)^{n-i}
    recon=sp.expand(sum(b[i]*sp.binomial(n,i)*h**i*(1-h)**(n-i) for i in range(n+1)))
    exact=sp.expand(recon-Q)==0
    print(f"degree n={n}: all Bernstein coeffs >=0 : {allpos}  (exact identity {exact}, min b_i={min(b)})")
    if allpos and exact:
        print(f"  => EXACT Bernstein/Handelman certificate: Q = sum_i b_i*C({n},i)*h^i*(1-h)^(n-i),")
        print(f"     all coeffs nonnegative, box products h^i(1-h)^(n-i)>=0 on [0,1]. Leaf discharge CERTIFIED.")
        break
