"""Verify gate: invariant battery, proved/refuted status flip, closure fixpoint.

This module is the SOLE path through which a node's status becomes `proved` or
`refuted`. Every other mutator (set_proof, promote_to_open, deprecate) is
explicitly prohibited from making that flip.

Key functions:
  normalize_lean     -- strip comments, collapse whitespace, drop trailing sorry
  statement_matches  -- normalized containment check (artifact contains statement)
  refutation_matches -- containment of refutation_statement (or ¬ + proposition)
  recompute_closures -- fixpoint over reduction-proved nodes; writes back to disk
  grant_status       -- the gate: flip open -> proved/refuted, raise GateError on fail
  verify_campaign    -- full invariant battery returning VerifyReport
"""
from __future__ import annotations

import dataclasses
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Optional

from .attempts import AttemptLog
from .claims import is_stale, load_claims
from .registry import Campaign, load_campaign
from .schema import Node, Proof, SchemaError, load_node, save_node, slug_of
from .statements import regen_diff, statement_path


# ---------------------------------------------------------------------------
# GateError
# ---------------------------------------------------------------------------

class GateError(Exception):
    """The verify gate rejected a status flip; node is left unchanged."""


# ---------------------------------------------------------------------------
# VerifyReport
# ---------------------------------------------------------------------------

@dataclass
class VerifyReport:
    errors: List[str]
    warnings: List[str]

    @property
    def ok(self) -> bool:
        return len(self.errors) == 0


# ---------------------------------------------------------------------------
# normalize_lean
# ---------------------------------------------------------------------------

def normalize_lean(text: str) -> str:
    """Strip Lean comments, collapse whitespace, drop trailing := by sorry / := sorry.

    Block comments (/- ... -/) are handled non-nestedly (sufficient for our
    artifact matching use-case; nested block comments in Lean 4 are legal but
    the payloads we deal with don't use them).
    """
    # Remove -- single-line comments (rest of line)
    text = re.sub(r"--[^\n]*", "", text)
    # Remove /- ... -/ block comments (non-greedy, non-nested)
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    # Collapse all whitespace runs to a single space
    text = re.sub(r"\s+", " ", text).strip()
    # Drop trailing := by sorry or := sorry
    text = re.sub(r"\s*:=\s*by\s+sorry\s*$", "", text).strip()
    text = re.sub(r"\s*:=\s*sorry\s*$", "", text).strip()
    return text


# ---------------------------------------------------------------------------
# statement_matches / refutation_matches
# ---------------------------------------------------------------------------

def _normalized_statement(node: Node, root: Path) -> str:
    """Derive the normalized statement for matching from the node's statement file.

    Per the controller ruling: read statement_path, drop the header line (the
    first line starting with '--'), drop import/open lines, normalize the rest.
    """
    path = statement_path(root, node)
    if not path.exists():
        # Fall back to the module name as a degenerate normalized form
        return normalize_lean(node.statement_module)

    text = path.read_text()
    lines = text.split("\n")

    # Drop header line (starts with --)
    if lines and lines[0].startswith("--"):
        lines = lines[1:]

    # Drop import/open lines
    body_lines = [
        l for l in lines
        if not l.strip().startswith("import ") and not l.strip().startswith("open ")
    ]

    return normalize_lean("\n".join(body_lines))


def statement_matches(artifact_text: str, node_statement: str) -> bool:
    """Return True iff normalize_lean(artifact_text) contains normalize_lean(node_statement)."""
    return normalize_lean(node_statement) in normalize_lean(artifact_text)


def refutation_matches(artifact_text: str, node: Node) -> bool:
    """Return True iff the artifact matches as a refutation.

    If node.refutation_statement is set: normalized containment.
    Otherwise: artifact must contain both '¬' and the normalized proposition.
    """
    norm_artifact = normalize_lean(artifact_text)
    if node.refutation_statement:
        return normalize_lean(node.refutation_statement) in norm_artifact
    # Fall back: require ¬ and the proposition
    norm_prop = normalize_lean(node.statement_module)
    return "¬" in norm_artifact and norm_prop in norm_artifact


# ---------------------------------------------------------------------------
# recompute_closures
# ---------------------------------------------------------------------------

def recompute_closures(campaign: Campaign) -> Dict[str, bool]:
    """Fixpoint: compute closure_clean for every node; write back to disk.

    Rules:
    - A direct-proved node's closure is always clean (True).
    - A reduction-proved node is clean iff every depends_on target has
      status 'proved' AND its own closure_clean is True.
    - Nodes without proof or with non-reduction via: unchanged (not in result).

    Returns a dict mapping slug -> bool for every node that has a proof link.
    Fixpoint iterates until stable.
    """
    # Build initial closure map from stored values
    closure: Dict[str, Optional[bool]] = {}
    for sl, node in campaign.nodes.items():
        if node.proof is None:
            continue
        if node.proof.via == "direct":
            closure[sl] = True
        else:
            closure[sl] = node.proof.closure_clean  # may be False initially

    # Fixpoint iteration
    changed = True
    while changed:
        changed = False
        for sl, node in campaign.nodes.items():
            if node.proof is None or node.proof.via != "reduction":
                continue
            # Compute fresh clean: all deps proved AND their closures clean
            all_clean = all(
                campaign.nodes.get(dep) is not None
                and campaign.nodes[dep].status == "proved"
                and closure.get(dep, False) is True
                for dep in node.depends_on
            )
            if all_clean != closure.get(sl, False):
                closure[sl] = all_clean
                changed = True

    # Write back any changes
    for sl, node in campaign.nodes.items():
        if node.proof is None:
            continue
        new_clean = closure.get(sl, node.proof.closure_clean)
        if new_clean != node.proof.closure_clean:
            new_proof = dataclasses.replace(node.proof, closure_clean=new_clean)
            new_node = dataclasses.replace(node, proof=new_proof)
            node_path = campaign.root / "nodes" / f"{sl}.toml"
            save_node(new_node, node_path)
            campaign.nodes[sl] = new_node

    return {sl: v for sl, v in closure.items() if v is not None}


# ---------------------------------------------------------------------------
# grant_status  -- THE GATE
# ---------------------------------------------------------------------------

def grant_status(campaign: Campaign, slug: str) -> Node:
    """The ONLY code path that flips a node to proved or refuted.

    Preconditions checked (GateError raised if any fail, status left unchanged):
    1. Node must be open.
    2. Node must have a proof link (proof field set).
    3. Artifact file must exist at campaign.root / node.proof.artifact.
    4. Artifact must match: statement_matches OR refutation_matches.
       - If statement_matches -> proved.
       - If only refutation_matches -> refuted.
       - If neither -> GateError.

    After flipping, recompute_closures is run on the campaign.

    Returns the updated Node.
    """
    node = campaign.nodes.get(slug)
    if node is None:
        raise GateError(f"Node {slug!r} not found in campaign.")

    if node.status != "open":
        raise GateError(
            f"Node {slug!r} has status {node.status!r}; "
            "grant_status only operates on open nodes."
        )

    if node.proof is None:
        raise GateError(
            f"Node {slug!r} has no proof link; call set_proof first."
        )

    artifact_path = campaign.root / node.proof.artifact
    if not artifact_path.exists():
        raise GateError(
            f"Node {slug!r}: artifact file {artifact_path} does not exist."
        )

    artifact_text = artifact_path.read_text()

    # Derive node statement from statement file
    norm_stmt = _normalized_statement(node, campaign.root)
    norm_artifact = normalize_lean(artifact_text)

    stmt_ok = norm_stmt in norm_artifact
    refut_ok = refutation_matches(artifact_text, node)

    if stmt_ok:
        new_status = "proved"
    elif refut_ok:
        new_status = "refuted"
    else:
        raise GateError(
            f"Node {slug!r}: artifact does not contain the node's statement "
            f"or refutation. Normalized statement: {norm_stmt!r}"
        )

    # Flip the status
    new_proof = dataclasses.replace(node.proof, closure_clean=(new_status == "proved"))
    new_node = dataclasses.replace(node, status=new_status, proof=new_proof)
    node_path = campaign.root / "nodes" / f"{slug}.toml"
    save_node(new_node, node_path)
    campaign.nodes[slug] = new_node

    # Update closure flags across the campaign
    recompute_closures(campaign)

    return campaign.nodes[slug]


# ---------------------------------------------------------------------------
# verify_campaign
# ---------------------------------------------------------------------------

def verify_campaign(
    root: Path,
    deep_lean: bool = False,
    runner: Optional[Callable] = None,
) -> VerifyReport:
    """Full invariant battery. Returns VerifyReport(errors, warnings, ok).

    Checks (errors unless noted as warnings):
    1. Schema: load_campaign parses all node/manifest files and checks acyclicity.
    2. Status coherence for proved/refuted nodes:
       a. Artifact file exists.
       b. statement or refutation matches.
       c. Closure flags consistent (recompute and compare).
    3. regen_diff clean for every node that has a statement file.
    4. Claims hygiene (WARNINGS): stale claims; claims on non-open nodes.
    5. Attempts ledger parses (errors on parse failure).
    6. Every deprecated node has a reason (caught by schema load).
    7. deep_lean: runs `lake build` in root/lean (never in unit tests).
    """
    root = Path(root)
    errors: List[str] = []
    warnings: List[str] = []

    # 1. Schema load + acyclicity
    try:
        campaign = load_campaign(root)
    except SchemaError as exc:
        errors.append(f"Schema error: {exc}")
        return VerifyReport(errors=errors, warnings=warnings)

    manifest = campaign.manifest

    # Recompute closures once to get a fresh picture for comparison
    fresh_closures = recompute_closures(campaign)

    # 2. Status coherence for proved/refuted nodes
    for sl, node in campaign.nodes.items():
        if node.status not in ("proved", "refuted"):
            continue

        # 2a. Artifact must exist
        if node.proof is None:
            errors.append(f"Node {sl!r}: status is {node.status!r} but proof is None.")
            continue

        artifact_path = root / node.proof.artifact
        if not artifact_path.exists():
            errors.append(
                f"Node {sl!r}: status is {node.status!r} but artifact "
                f"{node.proof.artifact!r} does not exist."
            )
            continue

        artifact_text = artifact_path.read_text()

        # 2b. Statement / refutation match
        norm_stmt = _normalized_statement(node, root)
        norm_artifact = normalize_lean(artifact_text)
        stmt_ok = norm_stmt in norm_artifact
        refut_ok = refutation_matches(artifact_text, node)

        if node.status == "proved" and not stmt_ok:
            errors.append(
                f"Node {sl!r}: status is 'proved' but artifact does not "
                f"contain the normalized statement."
            )
        elif node.status == "refuted" and not refut_ok:
            errors.append(
                f"Node {sl!r}: status is 'refuted' but artifact does not "
                f"match refutation criteria."
            )

        # 2c. Closure flag consistency (compare stored vs recomputed)
        if node.proof.via == "reduction":
            expected_clean = fresh_closures.get(sl, False)
            if node.proof.closure_clean != expected_clean:
                errors.append(
                    f"Node {sl!r}: stored closure_clean={node.proof.closure_clean} "
                    f"but recomputed value={expected_clean}."
                )

    # 3. regen_diff for every node with a statement file
    for sl, node in campaign.nodes.items():
        sp = statement_path(root, node)
        if sp.exists():
            diff = regen_diff(root, node, manifest)
            if diff:
                errors.append(f"Statement file drift: {diff}")

    # 4. Claims hygiene (WARNINGS)
    all_claims = load_claims(root)
    for claim_slug, claim_obj in all_claims.items():
        # Stale claim
        if is_stale(claim_obj):
            warnings.append(
                f"Stale claim on node {claim_slug!r} by session "
                f"{claim_obj.session!r}."
            )
        # Claim on non-open node
        node = campaign.nodes.get(claim_slug)
        if node is not None and node.status != "open":
            warnings.append(
                f"Claim on non-open node {claim_slug!r} "
                f"(status: {node.status!r})."
            )

    # 5. Attempts ledger (if it exists)
    ledger_path = root / "attempts.jsonl"
    if ledger_path.exists():
        log = AttemptLog(ledger_path)
        try:
            log.records()
        except Exception as exc:
            errors.append(f"Attempts ledger parse error: {exc}")

    # 7. deep_lean: run lake build (only when explicitly requested)
    if deep_lean:
        lean_dir = root / "lean"
        _runner = runner if runner is not None else subprocess.run
        try:
            result = _runner(
                ["lake", "build"],
                cwd=str(lean_dir),
                capture_output=True,
                text=True,
            )
            if result.returncode != 0:
                errors.append(
                    f"lake build failed (exit {result.returncode}): "
                    f"{result.stderr.strip()}"
                )
        except Exception as exc:
            errors.append(f"lake build error: {exc}")

    return VerifyReport(errors=errors, warnings=warnings)
