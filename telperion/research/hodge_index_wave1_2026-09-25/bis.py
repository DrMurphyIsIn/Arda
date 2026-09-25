def bis(f,a,b,tol=2e-3):
    fa=f(a); fb=f(b); assert fa>0>fb,(fa,fb)
    while b-a>tol:
        m=(a+b)/2; fm=f(m)
        if fm>0: a=m
        else: b=m
    return (a+b)/2
