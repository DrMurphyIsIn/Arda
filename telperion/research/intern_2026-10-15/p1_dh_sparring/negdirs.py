#!/usr/bin/env python3
"""Peak frequency of EVERY negative eigenvector for each coefficient surgery (companion to sparring.py)."""
import sys, math
import numpy as np
import sparring as sp

a = sys.argv[1] if len(sys.argv) > 1 else "2"
af = float(a)
n, h, A, M = sp.load_base(a)
N = int(math.floor(math.exp(2 * af)))
pen = sp.Pencil(A, M, sp.prime_mats(af, n, h, N))
sets, _ = sp.coeff_sets(N)
scale = float(np.abs(pen.eig(sets["DH"])[0]).max())
out = open(sp.os.path.join(sp.RES, "E1_negative_directions_a%s.txt" % a), "w")
for name, c in sets.items():
    w, U = pen.eig(c)
    neg = [(w[i], sp.fourier_peak(pen, af, n, h, U[:, i])[0]) for i in range(len(w)) if w[i] < -1e-10 * scale]
    line = "%-40s " % name + ("; ".join("%.3e @ t=%.1f" % x for x in neg) if neg else "none")
    print(line); out.write(line + "\n")
