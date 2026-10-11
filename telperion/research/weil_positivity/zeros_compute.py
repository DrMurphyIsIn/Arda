# Compute imaginary parts of zeta zeros n=2001..NMAX with mpmath.zetazero (dps 25), parallel.
import os, sys, json
os.environ.setdefault("OMP_NUM_THREADS","1")
import mpmath as mp
from multiprocessing import Pool
NMAX = int(sys.argv[1]) if len(sys.argv)>1 else 20000
def work(n):
    mp.mp.dps = 25
    return n, mp.nstr(mp.zetazero(n).imag, 22)
if __name__ == "__main__":
    base = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "zeros2000.json")))
    out = {i+1: s for i, s in enumerate(base)}
    with Pool(12) as p:
        for k, (n, s) in enumerate(p.imap_unordered(work, range(2001, NMAX+1), chunksize=20)):
            out[n] = s
            if k % 1000 == 0: print(k, flush=True)
    json.dump([out[i] for i in range(1, NMAX+1)], open("zeros%d.json" % NMAX, "w"))
    print("done", NMAX)
