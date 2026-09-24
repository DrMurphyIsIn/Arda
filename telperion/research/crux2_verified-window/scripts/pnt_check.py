# PNT continuum model of the window comb: kernel K(x,y) = exp(|x-y|/2) on L^2[-L,L] (midpoint Nystrom).
import numpy as np, math
for L in [2.0, 2.3, 4.0, 8.0]:
    for N in [1000, 2000]:
        h = 2*L/N; x = -L + h*(np.arange(N)+0.5)
        K = np.exp(np.abs(x[:,None]-x[None,:])/2)*h
        lam = np.linalg.eigvalsh(K)[-1]
        print(f"L={L} N={N}: lambda_max={lam:.6f}  lambda_max/e^L={lam/math.exp(L):.5f}  pointwise mass 2*int_0^(2L) e^(u/2) du /e^L = {4*(math.exp(L)-1)/math.exp(L):.4f}")
