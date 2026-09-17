"""Throughput bench for the Li ladder's ENCLOSURE side (Route B / B1; measurements in
docs/LI_LADDER_COST_MODEL_2026-09-17.md).

    python examples/li_positivity/bench_li_ladder.py out.jsonl 20,50,100,200,500,1000

For each N in the schedule: find the smallest working precision (doubling from 128 bits,
then bisecting to 32-bit granularity) at which EVERY rung n < N has an enclosure with
>= TARGET_BITS bits of relative accuracy, and record wall time, precision, the worst
rung's width, and the largest intermediate xi-series coefficient (cancellation).  One
JSON line per attempt; status MIN_PREC lines carry the minimal precision found.

This measures INSTRUMENTATION cost only.  A certified prefix of any length is not evidence
for RH (li_rh_iff_tail: the tail is still infinite).  conjecture1_proved = False.
"""
from __future__ import annotations

import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.li_coeff import enclose_li_coeffs  # noqa: E402

TARGET_BITS = 40   # ~12 significant decimals, the emitted literal precision


def _log2frac(q: Fraction) -> float:
    return math.log2(q.numerator) - math.log2(q.denominator)


def rel_bits(lo: Fraction, hi: Fraction) -> float:
    """Relative accuracy of the box in bits (inf for a point box)."""
    w = hi - lo
    mid = (hi + lo) / 2
    if w == 0:
        return float("inf")
    if mid == 0:
        return -_log2frac(w)
    return -_log2frac(w / abs(mid))


def xi_series_max_coeff_log2(count: int, prec_bits: int) -> float:
    """log2 of the largest |coefficient| of the xi(z/(z-1)) series — the cancellation the
    F'/F inversion has to absorb (mirrors li_coeff.enclose_li_coeffs's construction)."""
    from flint import acb, acb_series, ctx
    old_prec, old_cap = ctx.prec, ctx.cap
    try:
        ctx.prec = prec_bits
        ctx.cap = count + 1
        z = acb_series([0, 1])
        one = acb_series([1])
        g = -z * (one - z).inv()
        pi_log = acb.pi().log()
        xi = ((g - one) * (-(g / 2) * pi_log).exp() * (g / 2 + one).gamma() * g.zeta())
        mx = max(abs(float(c.real.mid())) for c in xi.coeffs())
    finally:
        ctx.prec, ctx.cap = old_prec, old_cap
    return math.log2(mx) if mx > 0 else float("-inf")


def _attempt(N: int, prec: int) -> tuple[bool, float, float, int, list | None]:
    t0 = time.perf_counter()
    try:
        boxes = enclose_li_coeffs(N, prec_bits=prec)
    except ValueError:  # self-check failure = garbage balls at too-low precision
        return False, time.perf_counter() - t0, float("-inf"), -1, None
    t = time.perf_counter() - t0
    bits = [rel_bits(lo, hi) for lo, hi in boxes]
    mb = min(bits)
    return mb >= TARGET_BITS, t, mb, bits.index(mb), boxes


def bench(schedule: list[int], out: Path, budget_s: float = 900.0) -> None:
    with out.open("a") as fh:
        def rec(d):
            fh.write(json.dumps(d) + "\n")
            fh.flush()
            print(d, flush=True)

        for N in schedule:
            prec, last_t = 128, 0.0
            while True:
                if last_t > budget_s:
                    rec({"N": N, "status": "SKIPPED_BUDGET", "last_prec": prec // 2, "last_t": last_t})
                    break
                ok, last_t, mb, worst, boxes = _attempt(N, prec)
                d = {"N": N, "prec": prec, "t": round(last_t, 3), "min_rel_bits": round(mb, 2),
                     "worst_rung": worst, "status": "OK" if ok else "TOO_WIDE"}
                if ok:
                    lo, hi = boxes[-1]
                    d["last_rung_mid"] = float((lo + hi) / 2)
                    d["last_rung_width_log2"] = round(_log2frac(hi - lo), 1)
                    d["all_lo_positive"] = all(lo > 0 for lo, _ in boxes)
                    d["xi_series_max_coeff_log2"] = round(xi_series_max_coeff_log2(N, prec), 2)
                rec(d)
                if not ok:
                    prec *= 2
                    continue
                # bisect the minimal OK precision to 32-bit granularity
                lo_p, hi_p, t_ok = (prec // 2 if prec > 128 else 0), prec, last_t
                while hi_p - lo_p > 32:
                    mid_p = ((lo_p + hi_p) // 2) // 32 * 32
                    okb, tb, _, _, _ = _attempt(N, mid_p)
                    if okb:
                        hi_p, t_ok = mid_p, tb
                    else:
                        lo_p = mid_p
                rec({"N": N, "min_ok_prec": hi_p, "t_at_min_ok_prec": round(t_ok, 3), "status": "MIN_PREC"})
                break


if __name__ == "__main__":
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("bench_li_ladder.jsonl")
    sched = [int(x) for x in (sys.argv[2] if len(sys.argv) > 2 else "20,50,100,200,500,1000").split(",")]
    budget = float(sys.argv[3]) if len(sys.argv) > 3 else 900.0
    bench(sched, out, budget)
