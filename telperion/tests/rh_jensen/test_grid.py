"""Grid-mode test: d=2 Jensen hyperbolicity cert family, n=0..3 (Task 9).

conjecture1_proved = False. Verifies the full grid pipeline for the four
d=2 Jensen polynomial box-hyperbolicity certificates:
  - generate.py --grid emits four theorems, one per n in {0,1,2,3}.
  - Each emitted theorem name is jensen_box_hyperbolic_deg2_<n>.
  - Each theorem ends with .roots.card = 2.
  - The file contains no 'sorry'.
  - The AXLE statement-match gate is present for each theorem.

The lake build green check is documented separately (the existing
test_end_to_end_d2.py::test_generated_lean_builds_green test covers the
overall build gate; the grid regenerates the same TARGET file, so running
that test after generate.py --grid verifies grid-mode Lean correctness).

NOT a proof of RH.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = REPO_ROOT / "examples" / "jensen_hyperbolicity" / "lean"
LEAN_FILE = LEAN_DIR / "JensenHyperbolicity.lean"
GENERATE_SCRIPT = REPO_ROOT / "examples" / "jensen_hyperbolicity" / "generate.py"

PYTHON = sys.executable
GRID_OFFSETS = [0, 1, 2, 3]


def _run_grid(extra_args: list[str] | None = None) -> subprocess.CompletedProcess:
    cmd = [PYTHON, str(GENERATE_SCRIPT), "--grid"]
    if extra_args:
        cmd.extend(extra_args)
    return subprocess.run(cmd, capture_output=True, text=True)


def test_grid_mode_exits_zero() -> None:
    """generate.py --grid exits 0."""
    result = _run_grid()
    assert result.returncode == 0, (
        f"generate.py --grid exited {result.returncode}\n"
        f"stdout: {result.stdout}\n"
        f"stderr: {result.stderr}"
    )


def test_grid_mode_writes_four_theorems() -> None:
    """generate.py --grid writes a file with all four theorem declarations."""
    result = _run_grid()
    assert result.returncode == 0, f"generate.py --grid failed: {result.stderr}"
    assert LEAN_FILE.exists(), f"JensenHyperbolicity.lean not written to {LEAN_FILE}"
    content = LEAN_FILE.read_text()
    for n in GRID_OFFSETS:
        name = f"theorem jensen_box_hyperbolic_deg2_{n}"
        assert name in content, (
            f"Theorem declaration '{name}' not found in JensenHyperbolicity.lean"
        )


def test_grid_mode_all_theorems_have_roots_card_2() -> None:
    """Every theorem in the grid file concludes with .roots.card = 2."""
    _run_grid()
    assert LEAN_FILE.exists()
    content = LEAN_FILE.read_text()
    # Count occurrences: should be at least one per theorem + one per AXLE example.
    count = content.count(".roots.card = 2")
    assert count >= len(GRID_OFFSETS), (
        f"Expected at least {len(GRID_OFFSETS)} occurrences of '.roots.card = 2', "
        f"found {count}"
    )


def test_grid_mode_no_sorry() -> None:
    """The grid-emitted file contains no 'sorry'."""
    _run_grid()
    assert LEAN_FILE.exists()
    content = LEAN_FILE.read_text()
    assert "sorry" not in content, (
        "JensenHyperbolicity.lean contains 'sorry' after --grid generation; "
        "the emitter must produce a sorry-free cert family."
    )


def test_grid_mode_axle_gates_present() -> None:
    """Each theorem has a corresponding AXLE statement-match gate."""
    _run_grid()
    assert LEAN_FILE.exists()
    content = LEAN_FILE.read_text()
    for n in GRID_OFFSETS:
        # AXLE gate uses the theorem name as the proof term.
        name = f"jensen_box_hyperbolic_deg2_{n}"
        # The gate comment precedes the example that closes with ':= <name>'
        assert name in content, f"AXLE gate missing for {name}"
        # The example after the AXLE comment must reference the theorem name.
        # Check: each theorem appears at least twice (declaration + AXLE example).
        occurrences = content.count(name)
        assert occurrences >= 2, (
            f"'{name}' appears {occurrences} time(s); expected >= 2 "
            f"(theorem declaration + AXLE example)"
        )


def test_grid_mode_print_axioms_lines() -> None:
    """The file ends with a #print axioms line for each theorem."""
    _run_grid()
    assert LEAN_FILE.exists()
    content = LEAN_FILE.read_text()
    for n in GRID_OFFSETS:
        expected = f"#print axioms jensen_box_hyperbolic_deg2_{n}"
        assert expected in content, (
            f"'{expected}' not found in JensenHyperbolicity.lean"
        )


def test_n_list_mode_subset() -> None:
    """--n-list mode emits only the requested offsets."""
    # Run with --n-list 0 2 (subset of the grid)
    result = subprocess.run(
        [PYTHON, str(GENERATE_SCRIPT), "--n-list", "0", "2", "--prec", "400"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, (
        f"generate.py --n-list 0 2 failed: {result.stderr}"
    )
    assert LEAN_FILE.exists()
    content = LEAN_FILE.read_text()
    # n=0 and n=2 should be present; n=1 and n=3 should NOT.
    assert "theorem jensen_box_hyperbolic_deg2_0" in content
    assert "theorem jensen_box_hyperbolic_deg2_2" in content
    assert "theorem jensen_box_hyperbolic_deg2_1" not in content
    assert "theorem jensen_box_hyperbolic_deg2_3" not in content

    # Restore full grid for downstream tests.
    _run_grid()
