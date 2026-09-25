#!/usr/bin/env python3
"""Build the Telperion Registry Explorer: one self-contained HTML page for GitHub Pages.

    python explorer/build.py            # rebuild data/*.json and docs/explorer/index.html
    python explorer/build.py --check    # exit 1 if the committed build is stale vs the registry

WHAT THIS IS.  A static explorer, modelled on the presentation of the Riemann Hypothesis
Explorer (Alvaro Lozano-Robledo, CC BY 4.0), for the Telperion missions registry with the
reverse-Dyson quasicrystal program (MIRRORMERE) in front.  It renders

  * the registry (every campaign, every node, status straight from the TOML files, read
    through the missions package -- never parsed here),
  * the falsification zoo (`examples/quasicrystal/zoo_data/zoo_verdicts.json`, Arb/interval
    orchestration, not kernel),
  * the Davenport-Heilbronn off-line inventory (`zoo_data/dh_zeros.json`, Arb-certified
    winding, not kernel),
  * the first 2000 zeta zero ordinates (`research/zeros2000.json`, mpmath `zetazero`: a FLOAT
    MODEL, not a certified inventory -- the certified Arb ladder needs python-flint, which
    this build does not require),
  * the 20 Arb-conditional Li rung lower bounds parsed out of the emitted
    `examples/li_positivity/lean/LiPositivity.lean`,
  * the wall constants (the hypothesis-free width 3/2000 from the registry statement of
    MM_gaussian_positivity_small_lam_3e3; the sharp envelope of E6Bridge16).

WHAT IT MUST NEVER DO.  Invent a status; present an Arb-conditional or conditional theorem
as a proof; drop the sentence `conjecture1_proved = False`.  The page and every data file
carry that sentence, every readback is labelled "self-attested" (every audit to date was
recorded by the same session family that wrote the node), and the honesty footer lists what
is not proved.

DETERMINISM.  The output depends only on the repository contents, so `--check` is a plain
byte comparison of a fresh in-memory build against the committed files, the same convention
as the example islands' `generate.py --check`.  No timestamps, no git metadata.
"""
from __future__ import annotations

import argparse
import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Optional

HERE = Path(__file__).resolve().parent            # telperion/explorer
TELPERION = HERE.parent                            # telperion
REPO = TELPERION.parent                            # repository root
sys.path.insert(0, str(TELPERION / "src"))

from telperion.missions.registry import load_universe, parse_dep  # noqa: E402
from telperion.missions import coverage  # noqa: E402

GITHUB_BLOB = "https://github.com/DrMurphyIsIn/Arda/blob/main/"
DATA_DIR = HERE / "data"
SRC_DIR = HERE / "src"
OUT_HTML = REPO / "docs" / "explorer" / "index.html"
CONJECTURE_SENTENCE = "conjecture1_proved = False"

#: Independence labels come from the registry's provenance fields (missions PR #607):
#: a readback's `independence` is "" or "unverified" for every audit written by the same
#: session family that authored the node (every audit up to 2026-09-24), and a node carries a
#: `[comparator]` record only when the independent Comparator judge (a separate checker
#: binary and a second kernel) has re-checked the registered statement against the artifact.
#: Nothing here is inferred: the page shows exactly what the TOML records.
INDEPENDENCE_LABEL = "self-attested"          # the legacy / unverified label
JUDGE_LABEL = "judge-verified"                # a recorded Comparator pass on the current artifact


def independence_label(node) -> str:
    """The honest label for a node's readback, from the registry's own fields."""
    comp = getattr(node, "comparator", None)
    if comp is not None and getattr(comp, "run_id", ""):
        return JUDGE_LABEL
    rb = node.readback
    raw = (getattr(rb, "independence", "") or "").strip().lower() if rb is not None else ""
    if raw in ("", "unverified", "self-attested"):
        return INDEPENDENCE_LABEL
    return raw


def provenance_block(node) -> dict:
    """Digest-pinned grant, Comparator and CI-run records, as the registry stores them.
    Identities and session ids are deliberately NOT published (they are e-mail addresses
    and session tokens); only their presence and dates are shown."""
    out = {}
    au = getattr(node, "author", None)
    out["author_recorded"] = bool(au and getattr(au, "identity", ""))
    g = getattr(node, "grant", None)
    out["grant"] = None if g is None else {
        "date": getattr(g, "date", ""),
        "gate_version": getattr(g, "gate_version", ""),
        "artifact_sha256": (getattr(g, "artifact_sha256", "") or "")[:16],
    }
    c = getattr(node, "comparator", None)
    out["comparator"] = None if c is None else {
        "run_id": getattr(c, "run_id", ""),
        "date": getattr(c, "date", ""),
        "theorem": getattr(c, "theorem", ""),
        "run_url": getattr(c, "run_url", ""),
    }
    ci = getattr(node, "ci_record", None)
    out["ci_record"] = None if ci is None else {
        "workflow": getattr(ci, "workflow", ""),
        "job": getattr(ci, "job", ""),
        "run_id": getattr(ci, "run_id", ""),
        "conclusion": getattr(ci, "conclusion", ""),
        "date": getattr(ci, "date", ""),
    }
    out["requires_ci_job"] = getattr(node, "requires_ci_job", "") or ""
    return out

STATUS_ORDER = ("proved", "open", "draft", "refuted", "deprecated")


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------

def _rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPO.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


_STATEMENT_HEADER = re.compile(r"^(--.*|import .*|open .*|set_option .*|noncomputable .*)$")


def _statement_text(campaign_root: Path, slug: str) -> str:
    """The verbatim registry statement (the theorem, hypotheses included) minus boilerplate.

    Lives at <campaign>/lean/Statements/<Slug>.lean, generated by `mission add`; the file is
    the node's hypotheses in the only authoritative form the registry has.  Missing file
    (goal/draft nodes authored without one) -> empty string.
    """
    p = campaign_root / "lean" / "Statements" / f"{slug}.lean"
    if not p.is_file():
        return ""
    lines = []
    for raw in p.read_text(encoding="utf-8").splitlines():
        if _STATEMENT_HEADER.match(raw.strip()) and not lines:
            continue
        lines.append(raw.rstrip())
    text = "\n".join(lines).strip()
    # The generated body ends in `:= by sorry` (a statement, not a proof); show the statement.
    text = re.sub(r"\s*:=\s*by\s+sorry\s*$", "", text)
    return text


def _coverage_label(artifact: Optional[Path], built: set, covered: Dict[Path, set]) -> dict:
    """How CI treats the artifact: module-covered / island-built-only / uncovered / not-judged."""
    if artifact is None:
        return {"label": "no-artifact", "jobs": []}
    resolved = artifact.resolve()
    jobs = sorted(covered.get(resolved, ()))
    if jobs:
        return {"label": "module-covered", "jobs": jobs}
    island = coverage.island_of(resolved)
    if island is None:
        return {"label": "not-judged", "jobs": []}
    if island in built:
        return {"label": "island-built-only", "jobs": []}
    return {"label": "uncovered", "jobs": []}


def build_registry() -> dict:
    uni = load_universe(TELPERION / "missions")
    built = coverage.ci_built_islands(REPO)
    covered = coverage.ci_covered_lean_files(REPO)
    campaigns = []
    nodes = []
    for cname in sorted(uni.campaigns):
        camp = uni.campaigns[cname]
        m = camp.manifest
        counts = {s: 0 for s in STATUS_ORDER}
        for sl in sorted(camp.nodes):
            n = camp.nodes[sl]
            counts[n.status] += 1
            deps = []
            for d in n.depends_on:
                dc, ds = parse_dep(d, cname)
                deps.append(f"{dc}:{ds}")
            art = None
            proof = None
            if n.proof is not None:
                art = camp.root / n.proof.artifact
                proof = {
                    "artifact": _rel(art),
                    "artifact_url": GITHUB_BLOB + _rel(art),
                    "artifact_exists": art.is_file(),
                    "artifact_kind": n.proof.artifact_kind,
                    "via": n.proof.via,
                    "closure_clean": bool(n.proof.closure_clean),
                    "fidelity_note": n.proof.fidelity_note,
                }
            readback = None
            if n.readback is not None:
                readback = {
                    "auditor": n.readback.auditor,
                    "date": n.readback.date,
                    "text": n.readback.text,
                    "independence": independence_label(n),
                }
            statement = _statement_text(camp.root, sl)
            title = n.title
            nodes.append({
                "id": f"{cname}:{sl}",
                "campaign": cname,
                "slug": sl,
                "name": n.name,
                "title": title,
                "kind": n.kind,
                "status": n.status,
                "is_goal": sl == m.goal_node,
                "depends_on": deps,
                "proof": proof,
                "readback": readback,
                "provenance": provenance_block(n),
                "statement": statement,
                # Word-boundary matches: "unconditional" must NOT light the conditional badge,
                # and "arbitrary" must not light the Arb badge.
                "conditional": bool(re.search(r"(?<![a-z])conditional", title.lower())
                                    or re.search(r"(?<![a-z])conditional", sl.lower())),
                "arb": bool(re.search(r"\barb\b", title, re.IGNORECASE)),
                "refutation_statement": n.refutation_statement,
                "deprecated_reason": n.deprecated_reason,
                "created": n.created,
                "updated": n.updated,
                "coverage": _coverage_label(art, built, covered),
                "extra_keys": sorted((n.extra or {}).keys()),
            })
        campaigns.append({
            "dir": cname,
            "name": m.name,
            "title": m.title,
            "description": m.description,
            "goal_node": m.goal_node,
            "toolchain": m.environment_toolchain,
            "mathlib_rev": m.environment_mathlib_rev,
            "sources": list(m.sources),
            "counts": counts,
            "n_nodes": sum(counts.values()),
        })
    total = {s: sum(c["counts"][s] for c in campaigns) for s in STATUS_ORDER}
    return {
        "conjecture1_proved": False,
        "note": (CONJECTURE_SENTENCE + ". Every status below is read from the registry TOML "
                 "through telperion.missions; nothing is inferred. A readback is labelled "
                 f"{INDEPENDENCE_LABEL} unless the registry records a Comparator judge pass "
                 f"on the current artifact, in which case it is labelled {JUDGE_LABEL}."),
        "independence_label": INDEPENDENCE_LABEL,
        "judge_label": JUDGE_LABEL,
        "campaigns": campaigns,
        "nodes": nodes,
        "totals": total,
        "ci_built_islands": sorted(built),
    }


# ---------------------------------------------------------------------------
# Plot data
# ---------------------------------------------------------------------------

def _load_json(p: Path):
    return json.loads(p.read_text(encoding="utf-8"))


def _li_rungs() -> List[dict]:
    """The 20 emitted rungs: certified lower bounds hlo, each an Arb enclosure HYPOTHESIS."""
    src = (TELPERION / "examples/li_positivity/lean/LiPositivity.lean").read_text(encoding="utf-8")
    out = []
    for m in re.finditer(r"theorem li_rung_(\d+) \(hlo : \(\((\d+) / (\d+)\) : ℝ\)", src):
        n = int(m.group(1))
        fr = Fraction(int(m.group(2)), int(m.group(3)))
        out.append({"n": n, "N": n + 1, "hlo": f"{fr.numerator}/{fr.denominator}",
                    "hlo_float": float(fr), "trust": "Arb-conditional (hlo is a hypothesis)"})
    out.sort(key=lambda r: r["n"])
    return out


def _von_mangoldt_table(limit: int) -> List[tuple]:
    """(n, Lambda(n)) for the prime powers n <= limit, by a plain sieve."""
    sieve = bytearray([1]) * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    out = []
    for p in range(2, limit + 1):
        if sieve[p]:
            lp = math.log(p)
            q = p
            while q <= limit:
                out.append((q, lp))
                q *= p
    out.sort()
    return out


def prime_abs(lam: float, table: List[tuple]) -> float:
    """primeAbs(lam) = 2 sum_n Lambda(n) n^{-1/2} |1 - (log n)^2/(4 lam)| e^{-(log n)^2/(8 lam)}
    (E6Bridge16), truncated at the table's limit.  A float model of an explicit series."""
    s = 0.0
    for n, ln in table:
        u = math.log(n)
        s += ln / math.sqrt(n) * abs(1 - u * u / (4 * lam)) * math.exp(-u * u / (8 * lam))
    return 2 * s


def envelope_sharp(lam: float, pa: float) -> float:
    """envelopeCsharp(lam) = 2 pi e^{primeAbs + 1/2} + sqrt((16 + 2 primeAbs)/lam) + 3/sqrt(lam) + 1."""
    return 2 * math.pi * math.exp(pa + 0.5) + math.sqrt((16 + 2 * pa) / lam) + 3 / math.sqrt(lam) + 1


def build_plots() -> dict:
    zeros_raw = _load_json(TELPERION / "research/zeros2000.json")
    zeros = [round(float(z), 9) for z in zeros_raw]
    dh = _load_json(TELPERION / "examples/quasicrystal/zoo_data/dh_zeros.json")
    zoo = _load_json(TELPERION / "examples/quasicrystal/zoo_data/zoo_verdicts.json")
    table = _von_mangoldt_table(2_000_000)
    lam_grid = [round(x, 4) for x in
                [0.001, 0.0015, 0.002, 0.003, 0.005, 0.0075, 0.01, 0.015, 0.02, 0.03, 0.05, 0.075,
                 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.55, 0.6, 0.65, 0.7, 0.8, 0.9,
                 1.0, 1.1, 1.2]]
    pa = [prime_abs(l, table) for l in lam_grid]
    envelope = [{"lam": l, "primeAbs": round(p, 6), "envelopeCsharp": envelope_sharp(l, p)}
                for l, p in zip(lam_grid, pa)]
    dh_zeros = [{"gamma": z["gamma_approx"], "beta": z["beta_approx"], "on_line": z["on_line"],
                 "winding": z["winding"], "re": z["re"], "im": z["im"]} for z in dh["zeros"]]
    return {
        "conjecture1_proved": False,
        "zeros": {
            "ordinates": zeros,
            "count": len(zeros),
            "source": "telperion/research/zeros2000.json (mpmath zetazero)",
            "trust": "float model; NOT the certified Arb ladder inventory (python-flint absent "
                     "at build time). Used for illustration only.",
        },
        "dh": {
            "t_max": dh["t_max"],
            "trust": dh["trust"],
            "on_line_count": dh["on_line_count"],
            "off_line_count": dh["off_line_count"],
            "density_model_formula": dh["density_model_formula"],
            "off_line_attempts": dh["off_line_attempts"],
            "zeros": dh_zeros,
            "source": "telperion/examples/quasicrystal/zoo_data/dh_zeros.json",
        },
        "zoo": {
            "t_max": zoo["t_max"],
            "objects": zoo["objects"],
            "clauses": zoo["clauses"],
            "matrix": zoo["matrix"],
            "variant_kill": zoo["variant_kill"],
            "object_meta": zoo["object_meta"],
            "trust": zoo["trust"],
            "forged_controls": zoo["forged_controls"],
            "w3a_notes": zoo["w3a_notes"],
            "a2_findings": zoo["a2_findings"],
            "governance_failures": zoo["governance_failures"],
            "source": "telperion/examples/quasicrystal/zoo_data/zoo_verdicts.json",
        },
        "li": {
            "rungs": _li_rungs(),
            "kernel_rungs_hypothesis_free": [0, 1, 2, 3, 4],
            "kernel_rungs_node": "rh:RH_li_rungs_lt_five",
            "rate_proved": {"formula": "n + 1 <= 3 pi T / 2", "node": "rh:RH_li_ladder_height"},
            "rate_sharp": {"formula": "n + 1 <= 2 pi (T - 1/2)", "node": "rh:RH_li_ladder_height_sharp"},
            "height_4000_node": "rh:RH_li_rungs_of_height_4000_sharp",
            "height_4000_trust": "conditional on the tiled certificate's Arb band hypotheses",
            "source": "telperion/examples/li_positivity/lean/LiPositivity.lean (hlo bounds), "
                      "lambda_N on the page is a float-model paired zero sum over the bundled "
                      "ordinates plus a smooth tail",
        },
        "wall": {
            "lam0_free": "3/2000",
            "lam0_free_float": 3 / 2000,
            "lam0_free_node": "mirrormere:MM_gaussian_positivity_small_lam_3e3",
            "lam0_old": 1e-7,
            "lam0_old_node": "mirrormere:MM_gaussian_positivity_small_lam",
            "ladder_floor_lam": 1.0,
            "ladder_floor_note": "one_le_lamThreshold (E6Bridge12): the drawn edge lam = 1 is the "
                                 "FLOOR of the true threshold lamThreshold(c, D, d, delta), which "
                                 "depends on the certified window; the region is schematic.",
            "ladder_heights": [
                {"T": 4000, "status": "rh:RH_li_rungs_of_height_4000_sharp is proved, conditional "
                                      "on the tiled certificate's Arb band hypotheses; "
                                      "anduril ladder nodes h280000 / 1e6 / 1e9 are open"},
                {"T": 640000, "status": "cited by WALL_MAP_2026-09-21 as the ladder height; the "
                                        "registry has NO proved node at this height"},
                {"T": 3e12, "status": "Platt-Trudgian 2021, literature, not in-kernel"},
            ],
            "envelope": envelope,
            "envelope_formula": "envelopeCsharp(lam) = 2 pi e^{primeAbs(lam) + 1/2} + "
                                "sqrt((16 + 2 primeAbs)/lam) + 3/sqrt(lam) + 1 (E6Bridge16)",
            "envelope_node": "mirrormere:MM_gaussian_positivity_envelope_sharp",
            "prime_table_limit": 2_000_000,
            "trust": "primeAbs is an explicit convergent series evaluated in floats, truncated "
                     "at n <= 2e6; F and Theta on the page are float sums over the first 2000 "
                     "ordinates (truncated, not enclosures).",
        },
    }


# ---------------------------------------------------------------------------
# Bundle
# ---------------------------------------------------------------------------

def _json_for_script(obj) -> str:
    """JSON safe inside a <script> element: escape '</' so no tag can close early."""
    s = json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    return s.replace("</", "<\\/")


def render_html(registry: dict, plots: dict) -> str:
    template = (SRC_DIR / "index.html").read_text(encoding="utf-8")
    css = (SRC_DIR / "explorer.css").read_text(encoding="utf-8")
    js = (SRC_DIR / "explorer.js").read_text(encoding="utf-8")
    for marker in ("/*__CSS__*/", "/*__REGISTRY__*/", "/*__PLOTS__*/", "/*__JS__*/"):
        if marker not in template:
            raise SystemExit(f"template is missing marker {marker}")
    html = template.replace("/*__CSS__*/", css)
    html = html.replace("/*__REGISTRY__*/", _json_for_script(registry))
    html = html.replace("/*__PLOTS__*/", _json_for_script(plots))
    html = html.replace("/*__JS__*/", js)
    if CONJECTURE_SENTENCE not in html:
        raise SystemExit("built page lost the sentence " + CONJECTURE_SENTENCE)
    return html


def build_all() -> Dict[str, str]:
    registry = build_registry()
    plots = build_plots()
    files = {
        str(DATA_DIR / "registry.json"): json.dumps(registry, indent=1, ensure_ascii=False, sort_keys=True) + "\n",
        str(DATA_DIR / "plots.json"): json.dumps(plots, indent=1, ensure_ascii=False, sort_keys=True) + "\n",
        str(OUT_HTML): render_html(registry, plots),
    }
    return files


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail if the committed build is stale")
    args = ap.parse_args(argv)
    files = build_all()
    if args.check:
        stale = []
        for path, content in files.items():
            p = Path(path)
            if not p.is_file() or p.read_text(encoding="utf-8") != content:
                stale.append(path)
        if stale:
            for s in stale:
                print(f"STALE: {s}")
            print("run `python telperion/explorer/build.py` and commit the result")
            return 1
        print("explorer: up to date")
        return 0
    for path, content in files.items():
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
        print(f"wrote {p.relative_to(REPO)} ({len(content.encode('utf-8'))} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
