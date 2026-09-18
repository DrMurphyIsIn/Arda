"""Program Anduril C1 -- parity + fallback gate for the multieval grid sweep.

Verifies that the FFT-amortized `_online_sweep_zero_count_grid` (Platt
`scaled_lambda_vec` multieval) produces the SAME on-line zero count as the
existing per-point `_online_sweep_zero_count_platt` on already-certified bands,
that the close-pair fallback recovers the correct count when the grid is too
coarse, and that the path degrades gracefully when the grid entry point is
unavailable.

The grid values are the same documented Arb ball class as `enclose_lambda`
(scaled by the strictly positive e^{pi t/4}, sign-preserving); the certificate
only ever consumes the COUNT of sign changes.  conjecture1_proved = False.

    python examples/zeta_zero_localization/test_grid_sweep.py
"""
from __future__ import annotations

import math
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import generate as G  # noqa: E402
import telperion.arb_platt as AP  # noqa: E402

# Already-certified bands (im_lo, im_hi, expected N).  The expected N is the
# rigorous edge N-difference N(hi)-N(lo); [27938,27969] is the close-pair band
# (min zero gap ~0.16 < the 0.25 primary grid spacing) that exercises the
# denser-grid retry / midpoint fallback.
CERTIFIED_BANDS = [
    (4000, 4040, 42),
    (12000, 12034, 41),
    (27969, 28000, 42),
    (27938, 27969, 42),  # close pair
]


def test_parity_and_timing() -> bool:
    ok = True
    print(f"{'band':<18}{'current':>9}{'grid':>7}{'truth':>7}"
          f"{'cur_s':>9}{'grid_s':>9}{'speedup':>9}  parity")
    for lo, hi, truth in CERTIFIED_BANDS:
        t0 = time.time()
        n_cur = G._online_sweep_zero_count_platt(lo, hi, 300)
        s_cur = time.time() - t0
        t0 = time.time()
        n_grid = G._online_sweep_zero_count_grid(lo, hi, 300)
        s_grid = time.time() - t0
        band_ok = (n_cur == n_grid == truth)
        ok = ok and band_ok
        print(f"[{lo},{hi}]".ljust(18)
              + f"{n_cur:>9}{n_grid:>7}{truth:>7}"
              + f"{s_cur:>8.2f}s{s_grid:>8.2f}s{s_cur / s_grid:>8.1f}x"
              + f"  {'OK' if band_ok else 'FAIL'}")
    return ok


def test_closepair_fallback() -> bool:
    """A coarse primary grid (spacing 0.5) must miss the [27938,27969] pair on
    the first call, then recover the correct count via the denser-grid retry."""
    orig = AP.platt_grid
    calls = [0]

    def thin_primary(im_lo, im_hi, **kw):
        calls[0] += 1
        kw.setdefault("spacing_den", 2)  # 0.5 spacing on the primary call
        return orig(im_lo, im_hi, **kw)

    AP.platt_grid = thin_primary
    try:
        n = G._online_sweep_zero_count_grid(27938, 27969, 300)
    finally:
        AP.platt_grid = orig
    ok = (n == 42 and calls[0] >= 2)
    print(f"close-pair fallback (thinned primary): n={n} (truth 42) "
          f"grid_calls={calls[0]} {'OK' if ok else 'FAIL'}")
    return ok


def test_graceful_unavailable() -> bool:
    """When the grid entry point is unavailable, `_grid` raises and
    `run_box_turing`'s try/except falls back to the per-point sweep."""
    orig = AP.platt_grid
    orig_avail = AP.PLATT_GRID_AVAILABLE

    def raise_grid(*a, **k):
        raise RuntimeError("grid unavailable (simulated)")

    AP.platt_grid = raise_grid
    AP.PLATT_GRID_AVAILABLE = False
    try:
        G._online_sweep_zero_count_grid(4000, 4040, 300)
        raised = False
    except RuntimeError:
        raised = True
    finally:
        AP.platt_grid = orig
        AP.PLATT_GRID_AVAILABLE = orig_avail
    print(f"graceful unavailable: _grid raises={raised} "
          f"(run_box_turing try/except then uses per-point path) "
          f"{'OK' if raised else 'FAIL'}")
    return raised


def main() -> int:
    if not AP.PLATT_GRID_AVAILABLE:
        print("SKIP: platt grid (scaled_lambda_vec) unavailable in this libflint")
        return 0
    results = [
        test_parity_and_timing(),
        test_closepair_fallback(),
        test_graceful_unavailable(),
    ]
    passed = all(results)
    print(f"\nC1 GRID SWEEP GATE: {'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
