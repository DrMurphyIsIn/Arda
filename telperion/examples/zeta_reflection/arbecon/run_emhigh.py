"""Compile + kernel-check one generated order-(2K+1) instance (gen_emhigh.py), recording per-module
kernel time (sum of `type checking took`, -Dprofiler), wall time and peak RSS.

usage: run_emhigh.py SUMMARY.json [PARALLEL]
env:   LOCK        the session's leanlock.sh (prefix for every Lean call)
       EMH_OLEAN   out-of-tree olean dir (must already hold EMZetaHigh, EMZetaHighEval and the
                   Probes/ArbEconomics_{Eval,Sound,Zeta} oleans when the island libs are not built)
writes SUMMARY.timing.json next to the summary.  conjecture1_proved = False.
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
LOCK = os.environ.get("LOCK", "")
OLEAN = os.environ.get("EMH_OLEAN", os.path.join(HERE, "olean_emh"))


def ms(v):
    v = v.strip()
    if v.endswith("ms"):
        return float(v[:-2])
    if v.endswith("s"):
        return float(v[:-1]) * 1000.0
    return float(v)


def lean_env():
    env = dict(os.environ)
    lp = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ISLAND, capture_output=True, text=True).stdout.strip()
    env["LEAN_PATH"] = lp + ":" + OLEAN
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ISLAND, capture_output=True, text=True).stdout.strip()
    return env, lean


ENV, LEAN = lean_env()


def run_file(mod, profile=True):
    src = os.path.join(ISLAND, mod.replace(".", "/") + ".lean")
    out_olean = os.path.join(OLEAN, mod.replace(".", "/") + ".olean")
    os.makedirs(os.path.dirname(out_olean), exist_ok=True)
    cmd = ["/usr/bin/time", "-l"] + ([LOCK] if LOCK else []) + [LEAN]
    if profile:
        cmd += ["-Dprofiler=true", "-Dprofiler.threshold=1"]
    cmd += ["-o", out_olean, src]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=ISLAND, capture_output=True, text=True, env=ENV)
    wall = time.time() - t0
    out = p.stdout + p.stderr
    kern = [ms(m.group(1)) for m in re.finditer(r"type checking took ([0-9.]+m?s)", out)]
    rss = re.search(r"(\d+)\s+maximum resident set size", out)
    real = re.search(r"([0-9.]+) real", out)
    errs = [l for l in out.splitlines() if "error" in l]
    return dict(module=mod, rc=p.returncode, kernel_ms=sum(kern), n_kernel=len(kern),
                wall_s=float(real.group(1)) if real else wall, rss=int(rss.group(1)) if rss else None,
                errors=errs[:8], olean_bytes=os.path.getsize(out_olean) if os.path.exists(out_olean) else None)


def main():
    summ = sys.argv[1]
    par = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    meta = json.load(open(summ))
    res = dict(meta=meta)
    res["cfg"] = run_file(meta["cfg_module"], profile=False)
    t0 = time.time()
    with ThreadPoolExecutor(max_workers=par) as ex:
        parts = list(ex.map(run_file, meta["parts"]))
    res["parts"] = parts
    res["wall_parts_s"] = time.time() - t0
    res["assembly"] = run_file(meta["assembly"], profile=True)
    res["kernel_ms_chunks"] = sum(p["kernel_ms"] for p in parts)
    res["n_decls_checked"] = sum(p["n_kernel"] for p in parts)
    res["us_per_term"] = res["kernel_ms_chunks"] * 1000.0 / meta["terms"]
    res["errors"] = [e for p in parts for e in p["errors"]] + res["cfg"]["errors"] + res["assembly"]["errors"]
    json.dump(res, open(summ.replace(".json", ".timing.json"), "w"), indent=1)
    asm = res["assembly"]
    print(json.dumps(dict(tag=meta["tag"], N=meta["N"], K=meta["K"], chunk_kernel_s=res["kernel_ms_chunks"] / 1000,
                          us_per_term=res["us_per_term"], parts_wall_s=sum(p["wall_s"] for p in parts),
                          asm_kernel_ms=asm["kernel_ms"], asm_wall_s=asm["wall_s"],
                          max_rss_GB=max((p["rss"] or 0) for p in parts) / 1e9, asm_rss_GB=(asm["rss"] or 0) / 1e9,
                          cfg_wall_s=res["cfg"]["wall_s"], olean_bytes=sum((p["olean_bytes"] or 0) for p in parts),
                          errors=res["errors"])))


if __name__ == "__main__":
    main()
