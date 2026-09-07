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
