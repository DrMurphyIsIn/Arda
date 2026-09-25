"""Closed-form certificate model (zeta side) for v_c = sum_i c_i cos(k_i u) 1_[-A,A], k_i A = pi (m_i + 1/2).
   Q(v_c) >= c^T Mcert c,  Mcert = (C_N - log pi) A I - sum_{j=0}^N J(j + 1/4) - P
   C_N = -gamma + H_N,  J_ii(b) = 2A 2b/(4b^2+k^2) + 2k^2 (1+E)/(4b^2+k^2)^2,
   J_ij(b) = 2 s k_i k_j (1+E)/((4b^2+k_i^2)(4b^2+k_j^2)),  E = e^{-4bA},  s = (-1)^{m_i+m_j},
   P_ii = sum_n (Lambda(n)/sqrt n) [(2A - y) cos(k y) + sin(k y)/k],
   P_ij = sum_n (Lambda(n)/sqrt n) 2 s [k_i sin(k_j y) - k_j sin(k_i y)]/(k_i^2 - k_j^2),  y = log n.
"""
import mpmath as mp
import numpy as np
from weilmodes import von_mangoldt, lambda_dh
mp.mp.dps = 40

def gij(A, ki, kj, mi, mj, y):
    if ki == kj:
        return (2*A - y) * mp.cos(ki*y) / 2 + mp.sin(ki*y) / (2*ki)
    s = (-1)**(mi + mj)
    return s * (ki*mp.sin(kj*y) - kj*mp.sin(ki*y)) / (ki**2 - kj**2)

def Jij(A, ki, kj, mi, mj, b):
    E = mp.exp(-4*b*A)
    if ki == kj:
        return 2*A*2*b/(4*b*b + ki*ki) + 2*ki*ki*(1+E)/(4*b*b+ki*ki)**2
    s = (-1)**(mi + mj)
    return 2*s*ki*kj*(1+E)/((4*b*b+ki*ki)*(4*b*b+kj*kj))

def model(q, ms, N, kind='zeta'):
    A = q * mp.pi
    ks = [mp.mpf(2*m+1)/(2*q) for m in ms]
    d = len(ks)
    x = mp.exp(2*A)
    nmax = int(mp.floor(x))
    w = von_mangoldt(nmax) if kind == 'zeta' else lambda_dh(nmax)
    P = mp.matrix(d, d); J = mp.matrix(d, d)
    for i in range(d):
        for j in range(d):
            P[i, j] = sum(w[n]/mp.sqrt(n) * 2 * gij(A, ks[i], ks[j], ms[i], ms[j], mp.log(n)) for n in range(2, nmax+1) if w[n] != 0)
            J[i, j] = sum(Jij(A, ks[i], ks[j], ms[i], ms[j], mp.mpf(jj) + mp.mpf(1)/4) for jj in range(N+1))
    if kind == 'zeta':
        CN = -mp.euler + mp.harmonic(N) - mp.log(mp.pi)
    else:
        CN = -mp.euler + mp.harmonic(N) + mp.log(5/mp.pi)   # placeholder: D uses psi(3/4+..) (different series)
    Mc = CN * A * mp.eye(d) - J - P
    return A, ks, Mc, J, P

if __name__ == '__main__':
    q = mp.mpf(9)/14
    for N in (25, 50, 100, 200, 400, 1000):
        A, ks, Mc, J, P = model(q, (54, 55), N)
        Mn = np.array([[float(Mc[i, j]) for j in range(2)] for i in range(2)]) / float(A)
        print('N=%4d  Mcert/A =' % N, Mn.tolist(), ' min eig %.6f' % np.linalg.eigvalsh(Mn)[0])
