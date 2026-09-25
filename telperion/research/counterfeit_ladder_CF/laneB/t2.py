import numpy as np, mpmath as mp, time, sys
from bcore import *
x = float(sys.argv[1]); A = mp.log(x)/2
for kind in ('ZK','E'):
    f = Form(A, kind)
    for par in (0,1):
        for bk in ('neumann','dirichlet'):
            row=[]
            for N in (16,32,64,128,256):
                Mr, Gr = real_sector(f, sector_basis(A, N, par, bk), par)
                row.append('%d:%+.7f'%(N, gmin(Mr,Gr)[0]))
            print(kind,'x=%g'%x,'par',par,bk[:4],' '.join(row), flush=True)
