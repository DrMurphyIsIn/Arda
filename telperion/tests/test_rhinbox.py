"""Build assertion for RHInBoxCore.lean.

Skips automatically when lake/Lean is not available on PATH.
"""
import os
import shutil
import subprocess
from pathlib import Path

import pytest

_LAKE_PATH = os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", "")
requires_lake = pytest.mark.skipif(
    shutil.which("lake", path=_LAKE_PATH) is None,
    reason="requires lake/Lean",
)


@requires_lake
def test_rh_in_box_core_builds():
    env = {**os.environ, "PATH": _LAKE_PATH}
    d = str(
        Path(__file__).resolve().parents[1]
        / "examples"
        / "zeta_zero_localization"
        / "lean"
    )
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "RHInBoxCore"], cwd=d, env=env, capture_output=True, text=True
    )
    assert r.returncode == 0, r.stderr


@requires_lake
def test_rh_in_box_analytic_builds():
    env = {**os.environ, "PATH": _LAKE_PATH}
    d = str(
        Path(__file__).resolve().parents[1]
        / "examples"
        / "zeta_zero_localization"
        / "lean"
    )
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "RHInBoxAnalytic"], cwd=d, env=env, capture_output=True, text=True
    )
    assert r.returncode == 0, r.stderr


@requires_lake
def test_rh_in_box_generic_and_regression_build():
    env = {**os.environ, "PATH": _LAKE_PATH}
    d = str(
        Path(__file__).resolve().parents[1]
        / "examples"
        / "zeta_zero_localization"
        / "lean"
    )
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "RHInBox"], cwd=d, env=env, capture_output=True, text=True
    )
    assert r.returncode == 0, r.stderr
