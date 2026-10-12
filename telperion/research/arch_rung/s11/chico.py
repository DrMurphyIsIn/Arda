"""Load S10's certified polynomial chiPoly (chiCo_i, i < 67) as exact Fractions.
Re-runs gen_s10.py (1.6 s) in-process and caches the result in chico.json, keyed by the
SHA-256 of ArchS10_Data.lean (a regenerated S10 invalidates the cache).
conjecture1_proved = False."""
import os, json, sys
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(HERE, "chico.json")

S10DATA = os.path.join(HERE, "../../../examples/rvm_bridge/lean/ArchS10_Data.lean")

def _s10hash():
    import hashlib
    return hashlib.sha256(open(S10DATA, "rb").read()).hexdigest()

def load():
    if os.path.exists(CACHE):
        d = json.load(open(CACHE))
        if d.get("s10sha") == _s10hash():
            return [F(n, m) for n, m in d["chiCo"]]
    g = {"__name__": "gen_s10", "__file__": os.path.join(HERE, "../s10/gen_s10.py")}
    old = sys.argv
    sys.argv = ["gen_s10.py", os.devnull]
    try:
        exec(open(g["__file__"]).read(), g)
    finally:
        sys.argv = old
    co = [p / (2 * g["EQ"]) for p in g["pco"]]
    json.dump({"s10sha": _s10hash(), "chiCo": [[c.numerator, c.denominator] for c in co]}, open(CACHE, "w"))
    return co

if __name__ == "__main__":
    co = load()
    print(len(co), [float(c) for c in co[:8]])
