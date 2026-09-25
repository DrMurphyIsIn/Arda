from thresh import *
import numpy as np
for x in [19.4,19.6,19.7,19.8,19.9,20.0]:
    A=0.5*log(x); row=[]
    for M in (40,60,80,100,120):
        _, g0, QE, QK = build_modes(x, basis(A,M,0,'N'), 0)
        row.append(lam_min(QE,g0))
    d=np.diff(row)
    # Aitken extrapolation on last three
    a,b,c=row[-3:]; den=(c-b)-(b-a)
    ait = c - (c-b)**2/den if abs(den)>1e-15 else c
    print(f"x={x}: "+"  ".join(f"{l:+.7f}" for l in row)+f"   Aitken {ait:+.7f}", flush=True)
