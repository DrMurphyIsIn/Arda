"""Tests for `telperion mission …` CLI subtree (Task M7).

Run from telperion/:
    python3 -m pytest tests/test_missions_cli.py -v
"""
from __future__ import annotations

import dataclasses
import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    MissionManifest, Node, Readback, Proof,
    load_node, save_manifest, save_node, slug_of,
)
from telperion.missions.statements import write_statement  # noqa: E402

DEMO_FIXTURE = Path(__file__).parent / "fixtures" / "missions" / "demo"

# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

def _manifest() -> MissionManifest:
    return MissionManifest(
        name="Demo.goal",
        title="Demo Campaign",
        description="A synthetic demonstration campaign for testing the registry.",
        goal_node="Demo_goal",
        environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0",
        sources=(),
    )


def make_demo_root(tmp_path: Path) -> tuple[Path, Path]:
    """Copy demo fixture into tmproot/demo/; return (missions_root, campaign_root)."""
    missions_root = tmp_path / "missions"
    missions_root.mkdir()
    campaign_root = missions_root / "demo"
    shutil.copytree(DEMO_FIXTURE, campaign_root)
    return missions_root, campaign_root


# ---------------------------------------------------------------------------
# T1: status exit 0 and shows node slugs
# ---------------------------------------------------------------------------

def test_mission_status_exit0_shows_nodes(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "status", "demo"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Demo_lemma_a" in out
    assert "Demo_lemma_b" in out


def test_mission_status_all_campaigns(tmp_path, capsys):
    """Status with no campaign argument iterates all campaigns."""
    mroot, _ = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "status"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Demo" in out


# ---------------------------------------------------------------------------
# T2: open-leaves shows Demo_lemma_a, hides after claim, --all shows again
# ---------------------------------------------------------------------------

def test_open_leaves_shows_lemma_a(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "open-leaves", "demo"])
    assert rc == 0
    out = capsys.readouterr().out
    # open_leaves prints node.name (e.g. "Demo.lemma_a") + title
    assert "Demo.lemma_a" in out or "Demo_lemma_a" in out


def test_open_leaves_hides_after_claim(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    # Claim Demo_lemma_a
    main(["mission", "--missions-root", str(mroot), "claim", "Demo_lemma_a",
          "--campaign", "demo", "--session", "sess-1"])
    capsys.readouterr()  # clear output

    rc = main(["mission", "--missions-root", str(mroot), "open-leaves", "demo"])
    assert rc == 0
    out = capsys.readouterr().out
    # Both the dotted name and slug form should be absent
    assert "Demo.lemma_a" not in out
    assert "Demo_lemma_a" not in out


def test_open_leaves_all_shows_claimed(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    # Claim Demo_lemma_a
    main(["mission", "--missions-root", str(mroot), "claim", "Demo_lemma_a",
          "--campaign", "demo", "--session", "sess-1"])
    capsys.readouterr()

    rc = main(["mission", "--missions-root", str(mroot), "open-leaves", "demo", "--all"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Demo.lemma_a" in out or "Demo_lemma_a" in out


# ---------------------------------------------------------------------------
# T3: add creates node + statement files; duplicate add exits 1
# ---------------------------------------------------------------------------

def test_add_creates_node_and_statement(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot), "add", "demo", "New.lemma_x",
        "--title", "New lemma X",
        "--kind", "lemma",
        "--statement", "theorem new_x : 1 = 1",
    ])
    assert rc == 0
    node_file = campaign_root / "nodes" / "New_lemma_x.toml"
    assert node_file.exists()
    node = load_node(node_file)
    assert node.status == "draft"
    assert node.title == "New lemma X"

    stmt_file = campaign_root / "lean" / "Statements" / "New_lemma_x.lean"
    assert stmt_file.exists()
    content = stmt_file.read_text()
    assert "new_x" in content


def test_add_duplicate_exits1(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    main([
        "mission", "--missions-root", str(mroot), "add", "demo", "Dup.lemma",
        "--title", "Dup", "--kind", "lemma", "--statement", "theorem dup : True",
    ])
    capsys.readouterr()
    rc = main([
        "mission", "--missions-root", str(mroot), "add", "demo", "Dup.lemma",
        "--title", "Dup again", "--kind", "lemma", "--statement", "theorem dup2 : True",
    ])
    assert rc == 1


def test_add_with_deps(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot), "add", "demo", "Dep.lemma_z",
        "--title", "Dep lemma Z", "--kind", "lemma",
        "--statement", "theorem dep_z : 1 = 1",
        "--deps", "Demo_lemma_a",
    ])
    assert rc == 0
    node = load_node(campaign_root / "nodes" / "Dep_lemma_z.toml")
    assert "Demo_lemma_a" in node.depends_on


# ---------------------------------------------------------------------------
# T4: audit records readback AND promotes draft -> open
# ---------------------------------------------------------------------------

def test_audit_records_readback_and_promotes(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    # Demo_lemma_b is draft; audit it
    rc = main([
        "mission", "--missions-root", str(mroot), "audit", "Demo_lemma_b",
        "--campaign", "demo",
        "--text", "Statement says lemma B holds.",
        "--auditor", "operator",
    ])
    assert rc == 0
    node = load_node(campaign_root / "nodes" / "Demo_lemma_b.toml")
    assert node.readback is not None
    assert node.readback.auditor == "operator"
    assert node.status == "open"


# ---------------------------------------------------------------------------
# T5: link then grant with matching artifact flips to proved
# ---------------------------------------------------------------------------

def test_link_then_grant_proves(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    manifest = _manifest()

    # Write a statement file for Demo_lemma_a
    from telperion.missions.registry import load_campaign
    camp = load_campaign(campaign_root)
    node = camp.nodes["Demo_lemma_a"]
    stmt = "theorem demo_lemma_a : 1 = 1"
    write_statement(campaign_root, node, stmt, manifest)

    # Write a matching artifact .lean file
    artifact_rel = "proof/Demo_lemma_a.lean"
    artifact_path = campaign_root / artifact_rel
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text(f"{stmt} := by rfl\n")

    # Link
    rc = main([
        "mission", "--missions-root", str(mroot), "link", "Demo_lemma_a",
        "--campaign", "demo",
        "--artifact", artifact_rel,
        "--kind", "lean_module",
        "--via", "direct",
    ])
    assert rc == 0
    # Status should still be open after link
    node_after_link = load_node(campaign_root / "nodes" / "Demo_lemma_a.toml")
    assert node_after_link.status == "open"

    # Grant
    rc2 = main([
        "mission", "--missions-root", str(mroot), "grant", "Demo_lemma_a",
        "--campaign", "demo",
    ])
    assert rc2 == 0
    node_after_grant = load_node(campaign_root / "nodes" / "Demo_lemma_a.toml")
    assert node_after_grant.status == "proved"


def test_grant_mismatched_artifact_exits1(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    manifest = _manifest()

    from telperion.missions.registry import load_campaign
    camp = load_campaign(campaign_root)
    node = camp.nodes["Demo_lemma_a"]
    stmt = "theorem demo_lemma_a : 1 = 1"
    write_statement(campaign_root, node, stmt, manifest)

    # Write artifact with WRONG statement
    artifact_rel = "proof/Demo_lemma_a.lean"
    artifact_path = campaign_root / artifact_rel
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text("theorem completely_different : 2 = 3 := by simp\n")

    main([
        "mission", "--missions-root", str(mroot), "link", "Demo_lemma_a",
        "--campaign", "demo",
        "--artifact", artifact_rel,
        "--kind", "lean_module",
        "--via", "direct",
    ])
    capsys.readouterr()

    rc = main([
        "mission", "--missions-root", str(mroot), "grant", "Demo_lemma_a",
        "--campaign", "demo",
    ])
    assert rc == 1
    node_after = load_node(campaign_root / "nodes" / "Demo_lemma_a.toml")
    assert node_after.status == "open"


# ---------------------------------------------------------------------------
# T6: verify exit 0 on clean fixture, exit 1 after injecting mismatch
# ---------------------------------------------------------------------------

def test_verify_clean_fixture(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "verify", "demo"])
    # Demo fixture has no proved nodes and no statement files, should be clean
    assert rc == 0


def test_verify_exits1_with_mismatch(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    manifest = _manifest()

    from telperion.missions.registry import load_campaign
    camp = load_campaign(campaign_root)
    node = camp.nodes["Demo_lemma_a"]
    stmt = "theorem demo_lemma_a : 1 = 1"
    write_statement(campaign_root, node, stmt, manifest)

    # Force proved status with a bad artifact (mismatched statement)
    artifact_rel = "proof/Demo_lemma_a.lean"
    artifact_path = campaign_root / artifact_rel
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    artifact_path.write_text("theorem wrong : 2 + 2 = 5 := by simp\n")

    # Directly write proved node with proof link to bypass grant gate
    proved_node = dataclasses.replace(
        node,
        status="proved",
        proof=Proof(
            artifact=artifact_rel,
            artifact_kind="lean_module",
            via="direct",
            closure_clean=True,
        ),
    )
    save_node(proved_node, campaign_root / "nodes" / "Demo_lemma_a.toml")

    rc = main(["mission", "--missions-root", str(mroot), "verify", "demo"])
    assert rc == 1


# ---------------------------------------------------------------------------
# T7: attempt appends a line to the ledger
# ---------------------------------------------------------------------------

def test_attempt_appends_line(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot),
        "attempt", "Demo_lemma_a",
        "--campaign", "demo",
        "--session", "sess-test",
        "--route", "direct_proof",
        "--verdict", "Stalled",
        "--detail", "Not enough time",
    ])
    assert rc == 0
    ledger = campaign_root / "attempts.jsonl"
    assert ledger.exists()
    import json
    lines = [json.loads(l) for l in ledger.read_text().splitlines() if l.strip()]
    assert len(lines) >= 1
    assert lines[-1]["verdict"] == "Stalled"
    assert lines[-1]["route"] == "direct_proof"


# ---------------------------------------------------------------------------
# T8: release removes the claim
# ---------------------------------------------------------------------------

def test_release_removes_claim(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    main(["mission", "--missions-root", str(mroot), "claim", "Demo_lemma_a",
          "--campaign", "demo", "--session", "sess-rel"])
    claim_file = campaign_root / "claims" / "Demo_lemma_a.toml"
    assert claim_file.exists()

    rc = main(["mission", "--missions-root", str(mroot), "release", "Demo_lemma_a",
               "--campaign", "demo", "--session", "sess-rel"])
    assert rc == 0
    assert not claim_file.exists()


# ---------------------------------------------------------------------------
# T9: graph outputs DOT to stdout
# ---------------------------------------------------------------------------

def test_graph_outputs_dot(tmp_path, capsys):
    mroot, _ = make_demo_root(tmp_path)
    rc = main(["mission", "--missions-root", str(mroot), "graph", "demo"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "digraph" in out
    assert "Demo_lemma_a" in out
