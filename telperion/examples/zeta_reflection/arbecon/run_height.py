"""Compile + kernel-check one generated height instance, recording per-part timing and RSS.

usage: run_height.py TAG [PARALLEL]      (reads $ARBECON_RUNS/<TAG>.json written by gen_height.py)
  1. compiles Probes/ArbEconomics_<TAG>_Cfg.lean -> olean (out-of-tree olean dir)
  2. runs each part Probes/ArbEconomics_<TAG>_P<j>.lean with -Dprofiler=true through leanlock.sh,
     /usr/bin/time -l, producing its olean too (for the assembly module)
  3. writes runs/<TAG>.timing.json : per-part kernel ms (sum of `type checking took`), wall s,
     max RSS bytes, and errors.
conjecture1_proved = False.
"""
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ISLAND = os.path.join(HERE, "..", "lean")
LEAN = os.path.join(HERE, "lean_probe.sh")
LOCK = os.environ.get("LOCK", "")              # e.g. the session's leanlock.sh
OLEAN = os.path.join(os.environ.get("ARBECON_OLEAN", os.path.join(HERE, "olean")), "Probes")
RUNS = os.environ.get("ARBECON_RUNS", os.path.join(HERE, "runs"))


def ms(v):
    v = v.strip()
    if v.endswith("ms"):
        return float(v[:-2])
    if v.endswith("s"):
        return float(v[:-1]) * 1000.0
    return float(v)


def run_file(mod, profile=True):
    src = os.path.join(ISLAND, "Probes", mod + ".lean")
    cmd = ["/usr/bin/time", "-l"] + ([LOCK] if LOCK else []) + [LEAN]
    if profile:
        cmd += ["-Dprofiler=true", "-Dprofiler.threshold=1"]
    cmd += ["-o", os.path.join(OLEAN, mod + ".olean"), src]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=ISLAND, capture_output=True, text=True)
    wall = time.time() - t0
    out = p.stdout + p.stderr
    kern = [ms(m.group(1)) for m in re.finditer(r"type checking took ([0-9.]+m?s)", out)]
    rss = re.search(r"(\d+)\s+maximum resident set size", out)
    real = re.search(r"([0-9.]+) real", out)
    errs = [l for l in out.splitlines() if "error" in l]
    return dict(module=mod, rc=p.returncode, kernel_ms=sum(kern), n_kernel=len(kern),
                wall_s=float(real.group(1)) if real else wall, rss=int(rss.group(1)) if rss else None,
                errors=errs[:5])


def main():
    tag = sys.argv[1]
    par = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    meta = json.load(open(os.path.join(RUNS, tag + ".json")))
    res = dict(tag=tag, meta=meta)
    res["cfg"] = run_file(meta["cfg_module"], profile=False)
    t0 = time.time()
    with ThreadPoolExecutor(max_workers=par) as ex:
        parts = list(ex.map(run_file, meta["parts"]))
    res["parts"] = parts
    res["wall_parts_s"] = time.time() - t0
    if meta.get("assembly"):
        res["assembly"] = run_file(meta["assembly"], profile=True)
    res["wall_total_s"] = time.time() - t0
    res["kernel_ms_total"] = sum(p["kernel_ms"] for p in parts)
    res["n_chunks_checked"] = sum(p["n_kernel"] for p in parts)
    res["max_rss"] = max((p["rss"] or 0) for p in parts)
    res["us_per_term"] = res["kernel_ms_total"] * 1000.0 / meta["terms"]
    res["errors"] = [e for p in parts for e in p["errors"]] + res["cfg"]["errors"] + (res["assembly"]["errors"] if "assembly" in res else [])
    json.dump(res, open(os.path.join(RUNS, tag + ".timing.json"), "w"), indent=1)
    asm = res.get("assembly", {})
    print(json.dumps(dict(tag=tag, kernel_s=res["kernel_ms_total"] / 1000, us_per_term=res["us_per_term"],
                          chunks=res["n_chunks_checked"], wall_parts=res["wall_parts_s"], wall=res["wall_total_s"],
                          max_rss_GB=res["max_rss"] / 1e9, asm_wall=asm.get("wall_s"), asm_kernel_ms=asm.get("kernel_ms"),
                          asm_rss_GB=(asm.get("rss") or 0) / 1e9, cfg_wall=res["cfg"]["wall_s"], errors=len(res["errors"]))))


if __name__ == "__main__":
    main()
