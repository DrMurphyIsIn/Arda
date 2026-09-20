"""The mirrormere island copies of the registry vocabulary must stay verbatim.

A node's statement is written against `missions/<campaign>/lean/Statements/*Defs.lean`.
The Lean that proves it lives in an island that re-declares those definitions rather than
importing them, and the grant gate matches statement against artifact by normalized text
containment.  If an island copy drifts, the gate still passes and the node still reads
`proved` while proving something about different constants.

`mirrormere` is gated here because its 31 mirrored declarations agree character for
character.  `rh`, `anduril` and `bg` are reported but not gated: their copies differ
cosmetically (namespace qualification, binder naming), which needs Lean-level comparison
to normalize.  See `missions/mirrors.py` for why a noisy gate would be worse than none.
"""
from pathlib import Path

import pytest

from telperion.missions.mirrors import check_mirrors, declarations, drifted

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples"
MMDEFS = ROOT / "missions" / "mirrormere" / "lean" / "Statements" / "MMDefs.lean"


@pytest.mark.skipif(not MMDEFS.is_file(), reason="mirrormere registry not present")
def test_mirrormere_island_copies_are_verbatim():
    rows = check_mirrors(MMDEFS, EXAMPLES)
    assert rows, "found no mirrored declarations at all -- the scan is broken, not the corpus"
    bad = drifted(rows)
    assert not bad, "island copies drifted from the mirrormere registry vocabulary:\n" + "\n".join(
        f"  {m.name} in {m.island_file}" for m in bad
    )


@pytest.mark.skipif(not MMDEFS.is_file(), reason="mirrormere registry not present")
def test_the_scan_actually_finds_the_known_mirrors():
    """A gate that silently matches nothing passes forever.  Pin what it must see."""
    names = {m.name for m in check_mirrors(MMDEFS, EXAMPLES)}
    for expected in ("twoFreq", "torusOrbit", "linearTorusForm", "defectFunctional",
                     "braggTerm", "zetaOrdinates", "RvMUnboundedMeanDensity"):
        assert expected in names, f"{expected} is mirrored in an island but the scan missed it"


def test_declaration_parser_does_not_swallow_a_modifier_line(tmp_path):
    """`omit [DecidableEq n] in` between two defs belongs to the NEXT one.

    Swallowing it made three identical `PosDefOn` copies compare unequal during
    development.  Every false positive here costs a real investigation, so it is pinned.
    """
    registry = tmp_path / "Defs.lean"
    registry.write_text("def f (x : Nat) : Nat :=\n  x + 1\n")
    island = tmp_path / "Island.lean"
    island.write_text(
        "def f (x : Nat) : Nat :=\n  x + 1\n\nomit [DecidableEq n] in\ntheorem g : True := trivial\n"
    )
    assert declarations(registry)["f"] == declarations(island)["f"]


def test_comments_do_not_count_as_drift(tmp_path):
    """The island annotates each copy with a `-- ===== MIRROR of ... =====` line."""
    registry = tmp_path / "Defs.lean"
    registry.write_text("def f (x : Nat) : Nat :=\n  x + 1\n")
    island = tmp_path / "Island.lean"
    island.write_text(
        "/-- doc -/\ndef f (x : Nat) : Nat :=\n  x + 1\n\n-- ===== MIRROR of Defs.lean:1-2 =====\n"
    )
    assert declarations(registry)["f"] == declarations(island)["f"]


def test_a_real_body_change_is_caught(tmp_path):
    registry = tmp_path / "Defs.lean"
    registry.write_text("def f (x : Nat) : Nat :=\n  x + 1\n")
    island = tmp_path / "Island.lean"
    island.write_text("def f (x : Nat) : Nat :=\n  x + 2\n")
    assert declarations(registry)["f"] != declarations(island)["f"]
