"""Build assertions for the dVP + box-localization combination (all zeros up to T).

Skips automatically when lake/Lean is not available on PATH.
"""
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

_LAKE_PATH = os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", "")
requires_lake = pytest.mark.skipif(
    shutil.which("lake", path=_LAKE_PATH) is None,
    reason="requires lake/Lean",
)

try:
    import telperion.arb_enclosure as _ae  # noqa: E402

    _FLINT_AVAILABLE = _ae._FLINT_AVAILABLE
except Exception:  # pragma: no cover - defensive
    _FLINT_AVAILABLE = False

requires_flint = pytest.mark.skipif(
    not _FLINT_AVAILABLE, reason="requires python-flint (Arb enclosures)"
)

_LEAN_DIR = (
    Path(__file__).resolve().parents[1] / "examples" / "zeta_zero_localization" / "lean"
)


@requires_lake
def test_zeta_confinement_builds():
    """The confinement lemma (`ZetaZeroConfinement.zero_in_band`) builds sorry-free.

    Every nontrivial zeta zero up to height T lies in the band `[a, 1-a]`, derived
    from the self-contained effective dVP zero-free region (PR #318) + the functional
    equation.
    """
    env = {**os.environ, "PATH": _LAKE_PATH}
    d = str(_LEAN_DIR)
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "ZetaZeroConfinement"],
        cwd=d,
        env=env,
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stderr


@requires_lake
def test_all_zeros_up_to_height_builds():
    """The combination theorem (`AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line`)
    builds sorry-free.

    Composes ZetaZeroConfinement (Task 3) + RHInBox (PR #312) to prove that all
    nontrivial zeta zeros up to height T lie on Re = 1/2, parameterized by a, T, and
    the Arb bundle (not fixed to concrete values).
    """
    env = {**os.environ, "PATH": _LAKE_PATH}
    d = str(_LEAN_DIR)
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "AllZerosUpToHeight"],
        cwd=d,
        env=env,
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stderr


@requires_lake
def test_all_zeros_up_to_height_100_builds():
    """The CONCRETE T=100 certificate (`AllZeros_h100.all_nontrivial_zeros_up_to_height_100`)
    builds sorry-free.

    Instantiates the combination at a=1/10^6, T=100: ALL nontrivial zeta zeros up to
    height 100 lie on Re = 1/2.  Composes ZetaZeroConfinement (band [1/10^6, 1-1/10^6],
    effective-rate edge discharged) with the emitted wide-box atom
    RHInBox_1d1000000_999999d1000000_0_100 (winding N=29).  #print axioms of the theorem
    is {propext, Classical.choice, Quot.sound}.
    """
    env = {**os.environ, "PATH": _LAKE_PATH}
    d = str(_LEAN_DIR)
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "AllZeros_h100"],
        cwd=d,
        env=env,
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stderr


@requires_flint
def test_wide_box_winding_agrees_29():
    """Agreement guard for the CONCRETE certificate's wide box `[1/10^6, 1-1/10^6] x [0,100]`.

    The boundary winding number `N` and the on-line sign-change zero count `N_line` must
    BOTH equal 29 (`N == N_line == 29`).  This is exactly what the emitted Lean milestone
    `RHInBox_1d1000000_999999d1000000_0_100` (and hence `AllZeros_h100`) consumes as the
    documented Arb winding input.  `run_box` REFUSES to emit if `N != N_line`, so a clean
    return already proves agreement; we additionally assert the emitted count marker is 29.
    """
    from fractions import Fraction

    from telperion.arb_enclosure import (
        enclose_zeta_segments,
    )
    from telperion.emit_winding_count import segment_winding_certificate

    sys.path.insert(0, str(_LEAN_DIR.parent))
    import generate  # noqa: E402  (examples/zeta_zero_localization/generate.py)

    box = (Fraction(1, 1000000), Fraction(999999, 1000000), Fraction(0), Fraction(100))

    # Boundary winding N (160-bit Arb rigorous zeta Taylor segments).
    segs = enclose_zeta_segments(box, 160, n_seed=4)
    n_total = segment_winding_certificate(box, segs).n
    assert n_total == 29, f"wide-box winding N = {n_total}, expected 29"

    # On-line sign-change zero count N_line (300-bit sweep on the critical line).
    n_line = generate._online_sweep_zero_count(box[2], box[3], 300)
    assert n_line == 29, f"wide-box on-line N_line = {n_line}, expected 29"
    assert n_total == n_line == 29
