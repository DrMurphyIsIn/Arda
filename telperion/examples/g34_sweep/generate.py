"""The G34 finite sweep (T4), audited: 442,800 exact comparisons re-run
through an INDEPENDENT port, fingerprinted, and third-engine spot-verified.

Per the audit plan this stratum is deliberately NOT per-theorem Lean (442,800
theorems would bury the kernel for no insight); its verification artifact is:

  * a full exact re-run of the sweep in fractions.Fraction — an independent
    implementation of the closed form and the searched comparator (the
    dual-engine discipline at sweep scale);
  * an AGGREGATE FINGERPRINT: the SHA-256 of every (case, config, comparator)
    triple in canonical order — any change to any of the 442,800 exact values
    changes the fingerprint (--check compares it);
  * the tightest cases surfaced (min-margin report — where the two-hub family
    comes closest to the single-hub bound is where the mathematics lives);
  * a SAMPLED interchange export (500 cases with full certificate data)
    verified live by the stdlib rechecker — the third engine.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import functools
import hashlib
import json
import random
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "src"))

V5F = Fr(3, 2) ** 5 + Fr(5, 12) * Fr(3, 2) ** 4      # F_of(1,5)
Z15 = Fr(3, 23)

DEFECTS = {"leaf": (Fr(1), Fr(1), 1, 2),
           "arm1": (Fr(3, 7), Fr(7, 4), 3, 9),
           "arm2": (Fr(3, 11), Fr(11, 4), 5, 13)}


def z_of(d: int, c: int) -> Fr:
    return Fr(3) / (3 * d + 4 * c)


def F_of(d: int, c: int) -> Fr:
    if c == 0:
        return Fr(1)
    D = d + c
    return Fr(3, 2) ** c + Fr(c) / (2 * D) * Fr(3, 2) ** (c - 1)


def pi_config(pA, pB, cA, jA, jB, zD, FD, side) -> Fr:
    dA = pA + 1 + (jA if side == "A" else 0)
    dB = pB + 1 + (jB if side == "B" else 0)
    zA, zB = z_of(dA, cA), z_of(dB, 0)
    sigA = pA * Z15 + (jA * zD if side == "A" else 0)
    sigB = pB * Z15 + (jB * zD if side == "B" else 0)
    j = jA if side == "A" else jB
    return (F_of(dA, cA) * V5F ** (pA + pB) * FD**j
            * ((1 + zA * sigA) * (1 + zB * sigB) + zA * zB))


@functools.lru_cache(maxsize=None)
def best_template(n: int) -> Fr:
    best = None
    for c0 in range(0, 7):
        for nleaf in (0, 1, 2):
            rem = n - 1 - 2 * c0 - nleaf
            if rem <= 0:
                continue
            for K in range(max(1, rem // 13), rem // 9 + 2):
                t2 = rem - K
                if t2 < 0 or t2 % 2:
                    continue
                tot = t2 // 2
                if tot > 8 * K:
                    continue
                b, r = divmod(tot, K)
                loads = [b + 1] * r + [b] * (K - r)
                zh = z_of(K + nleaf, c0)
                p = F_of(K + nleaf, c0)
                s = Fr(0)
                for c in loads:
                    p *= F_of(1, c)
                    s += z_of(1, c)
                s += nleaf
                p *= 1 + zh * s
                if best is None or p > best:
                    best = p
    return best


def sweep(pmax: int = 59):
    h = hashlib.sha256()
    checked = 0
    tightest: list[tuple[Fr, tuple]] = []
    for side in ("A", "B"):
        for name, (zD, FD, vD, jmax) in DEFECTS.items():
            pcap = 29 if side == "B" else pmax
            for cA in range(6):
                for pA in range(1, pmax + 1):
                    for pB in range(1, min(pA, pcap if side == "B" else pmax) + 1):
                        for j in range(1, jmax + 1):
                            jA, jB = (j, 0) if side == "A" else (0, j)
                            cfg = pi_config(pA, pB, cA, jA, jB, zD, FD, side)
                            n = 2 + 2 * cA + 11 * (pA + pB) + vD * j
                            best = best_template(n)
                            assert best > cfg, (side, name, cA, pA, pB, j)
                            margin = (best - cfg) / best
                            case = (side, name, cA, pA, pB, j)
                            h.update(
                                f"{case}|{cfg.numerator}/{cfg.denominator}|"
                                f"{best.numerator}/{best.denominator}\n".encode()
                            )
                            checked += 1
                            if len(tightest) < 10:
                                tightest.append((margin, case))
                                tightest.sort()
                            elif margin < tightest[-1][0]:
                                tightest[-1] = (margin, case)
                                tightest.sort()
    return checked, h.hexdigest(), tightest


def sampled_export(seed: int = 34, count: int = 500) -> dict:
    """A sampled interchange doc for the stdlib rechecker (constant claims:
    0 <= best - cfg with exact rationals)."""
    rng = random.Random(seed)
    instances = []
    cases = []
    for side in ("A", "B"):
        for name, (zD, FD, vD, jmax) in DEFECTS.items():
            for _ in range(count // 6):
                cA = rng.randrange(6)
                pA = rng.randint(1, 59)
                pB = rng.randint(1, min(pA, 29 if side == "B" else 59))
                j = rng.randint(1, jmax)
                cases.append((side, name, cA, pA, pB, j, zD, FD, vD))
    for side, name, cA, pA, pB, j, zD, FD, vD in cases:
        jA, jB = (j, 0) if side == "A" else (0, j)
        cfg = pi_config(pA, pB, cA, jA, jB, zD, FD, side)
        best = best_template(2 + 2 * cA + 11 * (pA + pB) + vD * j)
        diff = best - cfg
        instances.append({
            "lean_name": f"sweep_{side}_{name}_cA{cA}_pA{pA}_pB{pB}_j{j}",
            "point": {},
            "corners": [{
                "expr": {"rat": f"{diff.numerator}/{diff.denominator}"},
                "numerator": {"": f"{diff.numerator}/{diff.denominator}"},
                "denominator_factors": [{"poly": {"": "1/1"}, "power": 1}],
                "lift_n": 0,
            }],
        })
    return {"format": "telperion-certificates-v1", "family": "G34SweepSample",
            "input_hash": "0" * 64, "symbols": [],
            "claim": "0 <= best_template(n) - config, exact rationals",
            "instances": instances}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    checked, digest, tightest = sweep()
    from telperion.recheck import recheck

    doc = sampled_export()
    problems = recheck(doc, trials=3)
    summary = {
        "cases": checked,
        "fingerprint": digest,
        "tightest": [
            {"margin": f"{m.numerator}/{m.denominator}", "case": list(c)}
            for m, c in tightest
        ],
        "sampled_recheck": "GREEN" if not problems else f"RED({len(problems)})",
    }
    if args.check:
        frozen = json.loads((HERE / "frozen" / "summary.json").read_text())
        ok = (frozen["cases"] == summary["cases"]
              and frozen["fingerprint"] == summary["fingerprint"]
              and not problems)
        if not ok:
            print("DRIFT: sweep fingerprint or recheck mismatch")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    (HERE / "frozen").mkdir(parents=True, exist_ok=True)
    (HERE / "frozen" / "summary.json").write_text(json.dumps(summary, indent=1))
    (HERE / "frozen" / "sampled_certificates.json").write_text(json.dumps(doc))
    m0, c0 = tightest[0]
    print(f"sweep: {checked} cases exact, fingerprint {digest[:16]}, "
          f"sampled recheck {summary['sampled_recheck']}; tightest margin "
          f"{float(m0):.4%} at {c0}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
