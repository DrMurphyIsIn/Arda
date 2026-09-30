import numpy as np
def digamma(z):
    z = np.asarray(z, complex).copy(); acc = np.zeros_like(z)
    for _ in range(12):
        acc -= 1/z; z = z+1
    z2 = 1/(z*z)
    ser = np.log(z) - 0.5/z - z2*(1/12 - z2*(1/120 - z2*(1/252 - z2*(1/240 - z2*(1/132)))))
    return acc + ser
