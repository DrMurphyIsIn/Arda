"""Uniform-in-recursion monotone-tail (arm-dominance) tests."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion import ArmDominanceCertificate, arm_dominance_uniform  # noqa: E402

def test_arm_dominance_at_tie():
    assert ArmDominanceCertificate("t", 0, 5).check()

def test_arm_dominance_uniform_except_base():
    holds, exc = arm_dominance_uniform(range(0,4), range(0,8))
    assert exc == [(0,0)]                    # uniform except the single empty-hub base case

def test_arm_dominance_across_cherries():
    for cr in range(0,4):
        for k in range(1,6):
            assert ArmDominanceCertificate("t", cr, k).check()

def test_lean_emits_cross_multiplied():
    lean = ArmDominanceCertificate("t", 0, 5).lean()
    assert "norm_num" in lean and "≤" in lean and "ARM-DOMINANCE" in lean
