"""Cross-check of the Davenport-Heilbronn indefiniteness with an independent discretization.

weilop_legendre_ref.py (Legendre basis, double precision, full space = both parities) versus
wpw.py (cosine/sine bases, mpmath).  Double precision floors eigenvalues at ~1e-13, so only the
large negative eigenvalues (x >= 50) are comparable; the Legendre degree must be large enough to
resolve the ordinate 85.7 of the first off-line pair (degree ~ 200 on a window of length log x).
"""
import json
import time
import numpy as np
from weilop_legendre_ref import build

rows = []
for x, N in [(40, 150), (50, 150), (50, 200), (60, 200)]:
    t = time.time()
    H, P, phis, a = build(x, N, 'dh')
    ev = np.linalg.eigvalsh(H + P)
    row = dict(x=x, legendre_N=N, lowest=[float(v) for v in ev[:4]], seconds=round(time.time() - t, 1))
    rows.append(row)
    print(json.dumps(row), flush=True)
json.dump(rows, open('legendre_crosscheck.json', 'w'), indent=1)
