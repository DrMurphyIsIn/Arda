import numpy as np
from bcore import Form
from npdig import Omega
for x in (20, 22, 24):
    A = np.log(x)/2
    fm = Form(A, 'ZK'); AL = sum(2*abs(c) for (_, c, y) in fm.pr)
    T0 = 2*np.pi/np.sqrt(20)*np.exp((AL+8)/2)*1.2
    t = np.arange(0, T0, 0.002); C = np.zeros_like(t)
    for (_, c, y) in fm.pr: C += 2*c*np.cos(t*y)
    S = Omega(t, 'ZK') - C
    row = []
    for beta in (0.5, 1, 2, 3, 4, 5, 6):
        bad = np.where(S < beta)[0]; row.append('%g:%.0f' % (beta, t[bad[-1]]))
    print('x=%d A_L=%.2f  T_beta (last t with S<beta): %s   Omega(T0)=%.1f' % (x, AL, ' '.join(row), Omega(np.array([T0]),'ZK')[0]))
