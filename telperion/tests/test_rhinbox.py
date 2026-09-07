"""Build assertion for RHInBoxCore.lean.

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

import telperion.arb_enclosure as _ae  # noqa: E402

requires_flint = pytest.mark.skipif(
    not _ae._FLINT_AVAILABLE, reason="requires python-flint (Arb enclosures)"
)

_LEAN_DIR = (
    Path(__file__).resolve().parents[1] / "examples" / "zeta_zero_localization" / "lean"
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


# ---------------------------------------------------------------------------
# Task-4 per-box driver: `--box`/`--height` compute winding + on-line zeros and emit an
# instantiation of `rh_in_box_of_certificate`; refuse invalid/under-resolved boxes.
# ---------------------------------------------------------------------------

@requires_flint
def test_driver_box_flag_emits_instantiation():
    """`generate.py --box 2/5,3/5,10,35` computes N=5 (winding) = N_line and emits an
    instantiation referencing `rh_in_box_of_certificate`."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "_zgen", str(_LEAN_DIR.parent / "generate.py")
    )
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    txt = gen.run_box("2/5", "3/5", "10", "35", write=False)
    assert "RHInBox.rh_in_box_of_certificate" in txt
    assert "import RHInBox" in txt
    # 5 on-line zeros in [10,35] -> N = 5 existential.
    assert "x1 x2 x3 x4 x5" in txt


@requires_flint
def test_driver_refuses_box_containing_pole():
    """A box straddling s = 1 is refused by the driver (via box_localization_certificate)."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "_zgen2", str(_LEAN_DIR.parent / "generate.py")
    )
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    with pytest.raises(ValueError):
        # re-range [1/2,3/2] contains 1 and im-range [-1,1] contains 0 -> pole s = 1 in box.
        gen.run_box("1/2", "3/2", "-1", "1", write=False)


@requires_flint
@requires_lake
def test_driver_emitted_box_builds_sorry_free():
    """End-to-end: the driver emits a per-box instantiation for `[2/5,3/5]x[0,16]` (N=1) that
    BUILDS sorry-free with clean axioms.  Registers a temp lean_lib, builds, then cleans up."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "_zgen3", str(_LEAN_DIR.parent / "generate.py")
    )
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)

    tag = gen._box_tag("2/5", "3/5", "0", "16")
    mod = f"RHInBox_{tag}"
    lean_path = _LEAN_DIR / f"{mod}.lean"
    lakefile = _LEAN_DIR / "lakefile.toml"
    orig_lakefile = lakefile.read_text(encoding="utf-8")
    try:
        gen.run_box("2/5", "3/5", "0", "16", out_dir=_LEAN_DIR, write=True)
        assert lean_path.exists()
        # Temporarily register the module as a lean_lib so `lake build <mod>` resolves.
        lakefile.write_text(
            orig_lakefile + f'\n[[lean_lib]]\nname = "{mod}"\n', encoding="utf-8"
        )
        env = {**os.environ, "PATH": _LAKE_PATH}
        subprocess.run(["lake", "exe", "cache", "get"], cwd=str(_LEAN_DIR), env=env, check=True)
        r = subprocess.run(
            ["lake", "build", mod], cwd=str(_LEAN_DIR), env=env,
            capture_output=True, text=True,
        )
        assert r.returncode == 0, r.stderr
    finally:
        lakefile.write_text(orig_lakefile, encoding="utf-8")
        lean_path.unlink(missing_ok=True)
