import numpy as np
B2k = [1/6, -1/30, 1/42, -1/30, 5/66, -691/2730, 7/6, -3617/510]
def cdigamma(z):
    """complex digamma, numpy vectorized, Re z > 0."""
    z = np.asarray(z, complex); acc = np.zeros_like(z)
    w = z.copy()
    for _ in range(20):
        acc -= 1 / w; w = w + 1
    s = np.log(w) - 1 / (2 * w)
    w2 = w * w; p = w2
    for k, b in enumerate(B2k, 1):
        s -= b / (2 * k * p); p = p * w2
    return s + acc
def Omega(t, kind):
    t = np.asarray(t, float)
    if kind == 'zeta':
        return cdigamma(0.25 + 0.5j * t).real - np.log(np.pi)
    return cdigamma(0.25 + 0.5j * t).real + cdigamma(0.75 + 0.5j * t).real + np.log(20 / np.pi**2)
