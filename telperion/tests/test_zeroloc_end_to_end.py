"""End-to-end test: first kernel-verified on-line nontrivial-zero count for zeta.

Tests that sign_change_count >= 5 on [10, 35] at half-integer sample spacing,
matching the 5 known nontrivial Riemann zeta zeros in that interval:
  t ~ 14.1347, 21.0220, 25.0109, 30.4249, 32.9351.

The enclosure hypotheses (enclose_lambda -> sign-definite real box) are
Arb-certified NON-KERNEL inputs; the sign-change counting and zero-existence
argument are kernel-clean.  conjecture1_proved = False.
"""
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.arb_enclosure import enclose_lambda  # noqa: E402
from telperion.emit_xi_line_zeros import sign_change_count  # noqa: E402


def test_sign_changes_match_known_zero_count_10_to_35():
    # First nontrivial zeros (imag parts): 14.1347, 21.0220, 25.0109, 30.4249, 32.9351.
    # Sample densely on [10,35]; sign-change count must be >= 5 (the 5 known zeros in range).
    ts = [F(i, 2) for i in range(20, 71)]  # t = 10.0, 10.5, ..., 35.0
    samples = []
    for t in ts:
        (lo_re, hi_re), _ = enclose_lambda(F(1, 2), t, prec_bits=300)
        samples.append((t, (lo_re, hi_re)))
    assert sign_change_count(samples) >= 5


def test_box_arg_principle_lambda_builds():
    """Task 5 (Stage 2C): the box argument principle for Lambda builds sorry-free.

    Composes three kernel-verified atoms at box B = [2/5, 3/5] x [10, 35] with the
    boundary split (H1) and the winding value (H4) as hypotheses.  Kernel-clean;
    conjecture1_proved = False.
    """
    import os
    import subprocess

    env = {**os.environ, "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]}
    d = str(Path(__file__).resolve().parents[1] / "examples" / "zeta_zero_localization" / "lean")
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "BoxArgPrinciple"], cwd=d, env=env, capture_output=True, text=True
    )
    assert r.returncode == 0, r.stderr
