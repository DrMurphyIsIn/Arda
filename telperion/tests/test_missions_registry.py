"""Registry: campaign load, DAG, open-leaves, transitions, renders."""
import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.schema import (  # noqa: E402
    Claim, Node, Proof, Readback, SchemaError,
    load_node, save_node, slug_of,
)
from telperion.missions.registry import (  # noqa: E402
    Campaign, load_campaign, assert_acyclic,
    open_leaves, promote_to_open, deprecate, set_proof,
    render_status, render_dot,
)

DEMO_FIXTURE = Path(__file__).parent / "fixtures" / "missions" / "demo"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def copy_demo(tmp_path: Path) -> Path:
    """Copy the demo fixture into tmp_path and return the campaign root."""
    dest = tmp_path / "demo"
    shutil.copytree(DEMO_FIXTURE, dest)
    return dest


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def test_load_campaign_and_unknown_dep_raises(tmp_path):
    # Load the fixture; assert we get 4 nodes keyed by slug.
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)
    assert len(campaign.nodes) == 4
    assert "Demo_goal" in campaign.nodes
    assert "Demo_lemma_a" in campaign.nodes

    # Write a node whose depends_on points at a slug that does not exist.
    bad_node = Node(
        name="Demo.bad",
        title="Bad node",
        kind="lemma",
        status="draft",
        depends_on=("Nope",),
        statement_module="Statements.Demo_bad",
        created="2026-09-11",
        updated="2026-09-11",
    )
    save_node(bad_node, root / "nodes" / "Demo_bad.toml")
    with pytest.raises(SchemaError, match="Nope"):
        load_campaign(root)


def test_assert_acyclic_detects_cycle(tmp_path):
    # Create a two-node cycle: a -> b -> a.
    root = tmp_path / "cycle"
    root.mkdir()
    nodes_dir = root / "nodes"
    nodes_dir.mkdir()

    from telperion.missions.schema import MissionManifest, save_manifest
    save_manifest(MissionManifest(
        name="Cycle.goal",
        title="Cycle campaign",
        description="cycle test",
        goal_node="Cycle_a",
        environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0",
    ), root / "mission.toml")

    node_a = Node(
        name="Cycle.a", title="A", kind="lemma", status="draft",
        depends_on=("Cycle_b",), statement_module="Statements.Cycle_a",
        created="2026-09-11", updated="2026-09-11",
    )
    node_b = Node(
        name="Cycle.b", title="B", kind="lemma", status="draft",
        depends_on=("Cycle_a",), statement_module="Statements.Cycle_b",
        created="2026-09-11", updated="2026-09-11",
    )
    save_node(node_a, nodes_dir / "Cycle_a.toml")
    save_node(node_b, nodes_dir / "Cycle_b.toml")

    campaign = load_campaign(root)
    with pytest.raises(SchemaError) as exc_info:
        assert_acyclic(campaign)
    msg = str(exc_info.value)
    # Both slugs appear in the error message
    assert "Cycle_a" in msg
    assert "Cycle_b" in msg


def test_open_leaves_requires_deps_proved(tmp_path):
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)

    # Demo_lemma_a is open with no deps -> IS a leaf
    leaves = open_leaves(campaign)
    leaf_slugs = {n.name for n in leaves}
    assert "Demo.lemma_a" in leaf_slugs

    # Demo_goal is draft (not open) -> not a leaf regardless
    assert "Demo.goal" not in leaf_slugs

    # After lemma_a is proved and goal is opened, goal is a leaf only when b is also proved.
    # First prove lemma_a (set a proof on it).
    lemma_a = campaign.nodes["Demo_lemma_a"]
    proved_a = Node(
        **{f: getattr(lemma_a, f) for f in lemma_a.__dataclass_fields__
           if f not in ("status", "proof")},
        status="proved",
        proof=Proof("proof/Demo_lemma_a.lean", "lean_module", "direct", True),
    )
    save_node(proved_a, root / "nodes" / "Demo_lemma_a.toml")

    # Open Demo_goal by first recording a readback on Demo_lemma_b (draft), then
    # open Demo_goal directly by mutating its node file.
    goal = campaign.nodes["Demo_goal"]
    opened_goal = Node(
        **{f: getattr(goal, f) for f in goal.__dataclass_fields__
           if f not in ("status", "readback")},
        status="open",
        readback=Readback("Goal holds when both lemmas hold.", "operator", "2026-09-11"),
    )
    save_node(opened_goal, root / "nodes" / "Demo_goal.toml")

    campaign2 = load_campaign(root)

    # Demo_goal depends on Demo_lemma_b which is still draft -> not a leaf
    leaves2 = open_leaves(campaign2)
    leaf_slugs2 = {n.name for n in leaves2}
    assert "Demo.goal" not in leaf_slugs2

    # Now prove lemma_b too
    lemma_b = campaign2.nodes["Demo_lemma_b"]
    proved_b = Node(
        **{f: getattr(lemma_b, f) for f in lemma_b.__dataclass_fields__
           if f not in ("status", "proof", "readback")},
        status="proved",
        proof=Proof("proof/Demo_lemma_b.lean", "lean_module", "direct", True),
        readback=Readback("Lemma B holds.", "operator", "2026-09-11"),
    )
    save_node(proved_b, root / "nodes" / "Demo_lemma_b.toml")

    campaign3 = load_campaign(root)
    leaves3 = open_leaves(campaign3)
    leaf_slugs3 = {n.name for n in leaves3}
    # Now Demo_goal is open and both deps proved -> IS a leaf
    assert "Demo.goal" in leaf_slugs3


def test_promote_to_open_requires_readback(tmp_path):
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)

    # Demo_lemma_b is draft with no readback -> promote_to_open raises
    with pytest.raises(SchemaError, match="readback"):
        promote_to_open(campaign, "Demo_lemma_b")

    # Record a readback on Demo_lemma_b and reload
    lemma_b = campaign.nodes["Demo_lemma_b"]
    with_readback = Node(
        **{f: getattr(lemma_b, f) for f in lemma_b.__dataclass_fields__
           if f != "readback"},
        readback=Readback("Lemma B statement: auxiliary bound holds.", "operator", "2026-09-11"),
    )
    save_node(with_readback, root / "nodes" / "Demo_lemma_b.toml")
    campaign2 = load_campaign(root)

    # Now promote_to_open should succeed
    result = promote_to_open(campaign2, "Demo_lemma_b")
    assert result.status == "open"


def test_set_proof_never_sets_proved(tmp_path):
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)

    # Demo_lemma_a is already open; attach a proof -> status must remain "open"
    proof = Proof("proof/Demo_lemma_a.lean", "lean_module", "direct", True)
    result = set_proof(campaign, "Demo_lemma_a", proof)
    assert result.status == "open"
    assert result.proof is not None
    assert result.proof.artifact == "proof/Demo_lemma_a.lean"

    # Verify the file was saved with status "open"
    reloaded = load_node(root / "nodes" / "Demo_lemma_a.toml")
    assert reloaded.status == "open"
    assert reloaded.proof is not None


def test_render_status_contains_tree_and_statuses(tmp_path):
    root = copy_demo(tmp_path)
    campaign = load_campaign(root)
    output = render_status(campaign)

    # Output must contain the campaign title
    assert "Demo Campaign" in output

    # Must have one line per node (4 nodes)
    assert "Demo_goal" in output or "Demo.goal" in output
    assert "Demo_lemma_a" in output or "Demo.lemma_a" in output

    # Status glyphs must appear: draft=·, open=○, deprecated=†
    assert "·" in output   # draft glyph
    assert "○" in output   # open glyph
    assert "†" in output  # deprecated glyph (†)
