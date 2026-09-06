#!/usr/bin/env python3
"""shape_scout: the extraction+dedup core of the Telperion skill-extraction monitor.

Scans Lean proof corpora (BG and RH), extracts each theorem's GOAL, classifies it
into a Telperion emitter SHAPE, and separates:

  COVERED    theorem lives in an emitter-GENERATED file (telperion provenance
             header) -> already automated, nothing to do.
  CANDIDATE  hand-written theorem whose goal IS emitter-shaped -> a cross-
             pollination proposal: an existing emitter kind could (re)generate it.
  STRUCTURAL hand-written theorem that is NOT inequality/identity-shaped (encoder,
             def-bridge, forall-over-inductive, iff of structures) -> no emitter
             reaches it; needs human Lean.  (The `hConfine` bucket.)

This is the UNTRUSTED proposer only.  It never emits trusted Lean; it produces a
proposal queue for offline certification + CI-kernel confirmation.

Usage:
    python3 shape_scout.py <lean_root> [<lean_root> ...] [--json out.json]

Stdlib only.  Classification is structural/textual (no sympy, no Lean build).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# --- Telperion emitter-kind vocabulary (the shapes we can already discharge) ----
# Maps a shape label -> the emitter module/kind that handles it.  Anything not
# here is STRUCTURAL (not emitter-shaped).
EMITTER_FOR = {
    "identity":    "emit_facts.IdentityEmitter (kind=equation)",
    "polya_ineq":  "emit.DirectPolyaEmitter (kind=direct) / bilinear box",
    "sos_psd":     "emit_sos.SOSEmitter / psd_form / WorstCorner",
    "bracket":     "emit_bracket.IntervalBracketEmitter (kind=bracket)",
    "valuation":   "emit_padic (kind=valuation)",
    "trig_nonneg": "emit_sos_refutation / trig_nonneg (Markov-Lukacs)",
    "interlacing": "emit_interlacing (real-rootedness)",
    "unimodal":    "emit_unimodal (special=unimodal)",
    "witness":     "witness kind (existential comparator)",
    "monotone":    "emit_monotone_tail",
}

PROVENANCE = re.compile(r"/-\s*telperion", re.I)

# A Lean theorem/lemma header up to the goal-opening `:`.  We then bracket-scan.
THM = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)", re.M)

OPEN, CLOSE = "([{⟨", ")]}⟩"


def _strip_comments(src: str) -> str:
    """Remove Lean block (/- ... -/, nested) and line (-- ...) comments so that the
    word 'theorem' inside a docstring is never mistaken for a real declaration.
    Run AFTER provenance detection (which reads the raw header)."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if depth == 0 and two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if two == "/-":
            depth += 1
            i += 2
            continue
        if two == "-/" and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "".join(out)


_INT = re.compile(r"\d+")
_FREEVAR = re.compile(r"\(\s*[a-zA-Z]\w*\s*[:)]|\b[a-z]\w*\s+[a-z]\w*\b")

# Data-constructor token: `Type.ctor` (Branch.node, RTree.node, Equiv.swap) or a
# capitalized collection/constructor identifier used in constructor position
# (Multiset, `List.`).  Used to keep DEFINITIONAL recursion equations over
# inductive types (rfl/simp lemmas, NOT rational-function identities an emitter
# can reproduce) out of the `identity` CANDIDATE queue -- they are STRUCTURAL.
# Conservative: `Type.ctor` requires an UPPER-case type head so ordinary
# lower-case function application (`rRoot a i cs`, `Real.log`) is not caught.
_CONSTRUCTOR = re.compile(r"\b[A-Z][A-Za-z0-9_]*\.[a-z]|\bMultiset\b|\bList\.")


def is_trivial(goal: str, shape: str) -> bool:
    """All-numeric constant fact closable by norm_num/decide -> NOT an emitter gap.
    Large-integer valuation/identity facts are kept genuine (emit_padic / IdentityEmitter
    handle them better than raw norm_num, and they are the real BG tie signal)."""
    if shape in ("valuation",):
        return False
    if _FREEVAR.search(goal):
        return False
    ints = [int(m.group()) for m in _INT.finditer(goal)]
    big = any(v > 10_000 for v in ints)
    return not big  # all-numeric AND no big integer -> trivial norm_num fact


def _extract_goal(src: str, start: int) -> tuple[str, str] | None:
    """From the char index just after a theorem NAME, return (name-less) GOAL text
    and the tactic head, by depth-0 scanning for the goal-opening ':' then ':='."""
    depth = 0
    i = start
    goal_start = None
    n = len(src)
    while i < n:
        c = src[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and c == ":" and src[i:i + 2] != ":=":
            goal_start = i + 1
            break
        i += 1
    if goal_start is None:
        return None
    # find depth-0 ':=' ending the goal
    depth = 0
    j = goal_start
    while j < n:
        c = src[j]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and src[j:j + 2] == ":=":
            goal = src[goal_start:j]
            tac = src[j + 2:j + 60].strip().split("\n")[0]
            return goal.strip(), tac
        j += 1
    return None


def classify(goal: str) -> str:
    """Structural heuristics -> shape label.  Order matters (most specific first)."""
    g = goal
    # p-adic / divisibility
    if re.search(r"∣|padicVal|factorization|Nat\.gcd|Coprime", g):
        return "valuation"
    # PSD / matrices / minors
    if re.search(r"PosSemidef|Matrix|\bdet\b|Gram|minor|IsHermitian", g):
        return "sos_psd"
    # SOS / pseudo-expectation nonnegativity-on-squares: `0 ≤ pe(.. ^ 2)` (SoS-3XOR
    # / P-vs-NP lane) is an SOS certificate shape, NOT interlacing -- route to the
    # same SOS engine BG's bulk-discharge and RH's zero-free region use.
    if re.search(r"0\s*≤", g) and re.search(r"\bpe\b|pseudo|Expect", g) and "^ 2" in g:
        return "sos_psd"
    # bracket: two-sided enclosure of a transcendental
    if re.search(r"sqrt|Real\.exp|Real\.log|π|Real\.pi|Gamma|zeta|ζ", g) and (
        g.count("≤") + g.count("<") >= 2 or "∧" in g
    ):
        return "bracket"
    # nonneg trig
    if re.search(r"cos|sin", g) and re.search(r"0\s*≤|≥\s*0", g):
        return "trig_nonneg"
    # real-rootedness / interlacing
    if re.search(r"roots|Polynomial|interlac|hyperbolic|separ", g, re.I):
        return "interlacing"
    # unimodal / single-crossing
    if re.search(r"unimodal|StrictMono.*StrictAnti|crosses", g, re.I):
        return "unimodal"
    # existential witness
    if re.search(r"^\s*∃|\b∃", g):
        return "witness"
    # identity: a top-level '=' that is not ≤/≥/≠/≈ and not an iff
    eqs = re.findall(r"(?<![≤≥≠<>:=])=(?![=])", g)
    if eqs and "↔" not in g and not re.search(r"≤|<|≥|>", g):
        # DEFINITIONAL recursion equation over an inductive type (either side
        # mentions a data constructor, e.g. `rho0 (Branch.node c ch) = ...`)?
        # That is a rfl/simp lemma, not a rational-function identity the
        # IdentityEmitter can reproduce -> STRUCTURAL, not a CANDIDATE.
        # Pure arithmetic identities over ℚ/ℝ (no constructor token) stay `identity`.
        if _CONSTRUCTOR.search(g):
            return "structural"
        return "identity"
    # monotone tail
    if re.search(r"Monotone|Antitone|Tendsto|tail", g):
        return "monotone"
    # generic polynomial/rational inequality over reals
    if re.search(r"≤|<|≥|>", g) and re.search(r"ℝ|ℚ|\(\s*x|\by\b", g):
        return "polya_ineq"
    # structural: iff of props, forall over inductive, function/encoder, set eq
    return "structural"


@dataclass
class ThmRec:
    name: str
    file: str
    shape: str
    emitted: bool
    goal_excerpt: str
    goal_full: str = ""  # untruncated goal (one-line normalized) for --certify


@dataclass
class Report:
    thms: list[ThmRec] = field(default_factory=list)

    def scan_file(self, path: Path):
        raw = path.read_text(errors="replace")
        emitted = bool(PROVENANCE.search(raw[:400]))
        src = _strip_comments(raw)
        for m in THM.finditer(src):
            name = m.group(1)
            res = _extract_goal(src, m.end())
            if not res:
                continue
            goal, _tac = res
            shape = classify(goal)
            flat = re.sub(r"\s+", " ", goal).strip()
            self.thms.append(ThmRec(
                name=name, file=path.name, shape=shape, emitted=emitted,
                goal_excerpt=flat[:110], goal_full=flat,
            ))

    def buckets(self):
        covered, candidate, structural, trivial = [], [], [], []
        for t in self.thms:
            if t.emitted:
                covered.append(t)
            elif t.shape == "structural":
                structural.append(t)
            elif is_trivial(t.goal_excerpt, t.shape):
                trivial.append(t)
            else:
                candidate.append(t)
        return covered, candidate, structural, trivial


# ===========================================================================
# --certify : offline round-trip.  "emitter-SHAPED" != "emitter-REPRODUCIBLE".
# For CANDIDATE goals in a tractable arithmetic fragment, translate the Lean
# goal text into a sympy expression and actually run the check an emitter would
# rely on:
#   * identity goal `LHS = RHS`  -> sympy.simplify(LHS - RHS) == 0  (this is
#     exactly what Telperion's `equation`-kind certify validates).
#   * inequality `0 <= E` / `A <= B` / `A < B` -> Telperion's real Polya
#     positivity certify (`telperion.certify.polya_certify`) over the nonneg
#     orthant in x, y; if that refuses, a HEURISTIC numeric sampling fallback.
# Everything with function symbols / transcendentals / constructors / unknown
# identifiers is OUT-OF-FRAGMENT (not attempted, NOT a failure).
# ===========================================================================

# Free symbols the fragment admits (declared nonnegative for Polya).  Any OTHER
# alphabetic identifier => out-of-fragment (it is a function symbol or unknown).
_ALLOWED_SYMS = ("x", "y")

# Tokens that immediately disqualify a goal from the arithmetic fragment.
_OUT_OF_FRAGMENT = re.compile(
    r"∑|∏|∫|√|Real\.|Complex\.|riemannZeta|Gamma|Nat\.|Int\.|Finset|Multiset|"
    r"List\.|Matrix|max\b|min\b|∣|∀|∃|↔|→|if\b|then\b|fun\b|λ|‖|⌊|⌈|"
    r"[A-Z][A-Za-z0-9_]*\.[a-z]|::"
)


def _lean_to_sympy_str(side: str) -> str:
    """Turn one Lean arithmetic side into a python/sympy-eval string, or raise
    ValueError if it leaves the fragment.  Handles: `(a : ℚ)/b`, `(a:ℝ)`,
    bare ints, + - * / ^ (=> **), parentheses, and free symbols x, y.

    The result is eval'd in a namespace containing ONLY sympy Rational + the two
    symbols, so a stray identifier raises NameError even if it slips past here.
    """
    s = side.strip()
    # strip type ascriptions:  (E : ℚ)  ->  (E)   ;  bare `: ℝ` / `: ℚ` -> ''
    s = re.sub(r":\s*[ℚℝℤℕ]", "", s)
    s = s.replace("ℚ", "").replace("ℝ", "").replace("ℤ", "").replace("ℕ", "")
    # power operator
    s = s.replace("^", "**")
    # reject anything outside the arithmetic grammar (after ascription strip):
    #   digits, the two allowed symbols, operators, parens, whitespace, dot(float)
    leftover = re.sub(r"[0-9xy\s()+\-*/.]", "", s)
    if leftover:
        raise ValueError(f"non-arithmetic token(s): {sorted(set(leftover))!r}")
    # bare-integer literals as sympy Rationals so `64/621` is exact, not float
    s = re.sub(r"(?<![\w.])(\d+)(?![\w.])", r"Rational(\1)", s)
    if not s.strip():
        raise ValueError("empty side")
    return s


def _eval_side(side: str, sp, syms):
    ns = {"Rational": sp.Rational, "x": syms["x"], "y": syms["y"]}
    code = _lean_to_sympy_str(side)
    return eval(code, {"__builtins__": {}}, ns)  # noqa: S307 (namespace-restricted, own corpus)


def _split_relation(goal: str):
    """Return (lhs, rel, rhs) for a single top-level relation, or None.
    Rejects two-sided brackets `A < e ∧ e < B` (they carry '∧')."""
    if "∧" in goal or "↔" in goal:
        return None
    for rel in ("≤", "<", "="):
        # split on the FIRST occurrence of this relation that is not part of :=/==
        idx = goal.find(rel)
        if idx < 0:
            continue
        if rel == "=" and (goal[idx - 1:idx] in "≤<>≥≠:" or goal[idx + 1:idx + 2] == "="):
            continue
        return goal[:idx].strip(), rel, goal[idx + 1:].strip()
    return None


def certify_candidate(goal: str):
    """Attempt an offline round-trip of one CANDIDATE goal.

    Returns a dict {status, check, detail} where status is one of:
      reproduced   -- identity simplifies to 0, or inequality carries a Polya
                      certificate (or heuristic sampling found no violation).
      contradicted -- identity does NOT simplify to 0, or sampling found a
                      negative point => RED FLAG (misclassification or a
                      genuinely non-reproducible goal).
      out_of_fragment -- has function symbols/transcendentals/etc; not attempted.
    """
    if _OUT_OF_FRAGMENT.search(goal):
        return {"status": "out_of_fragment", "check": "-", "detail": "non-arithmetic token"}
    rel = _split_relation(goal)
    if rel is None:
        return {"status": "out_of_fragment", "check": "-", "detail": "no single relation / bracket"}
    lhs, op, rhs = rel
    try:
        import sympy as sp
    except ImportError:
        return {"status": "out_of_fragment", "check": "-", "detail": "sympy unavailable"}
    syms = {"x": sp.Symbol("x", nonnegative=True), "y": sp.Symbol("y", nonnegative=True)}
    try:
        L = _eval_side(lhs, sp, syms)
        R = _eval_side(rhs, sp, syms)
    except (ValueError, NameError, SyntaxError, TypeError, ZeroDivisionError) as e:
        return {"status": "out_of_fragment", "check": "-", "detail": f"translate: {e}"}

    if op == "=":
        try:
            zero = sp.simplify(L - R) == 0
        except Exception as e:  # noqa: BLE001
            return {"status": "out_of_fragment", "check": "sympy.simplify", "detail": str(e)}
        if zero:
            return {"status": "reproduced", "check": "sympy.simplify(LHS-RHS)==0",
                    "detail": "identity"}
        return {"status": "contradicted", "check": "sympy.simplify(LHS-RHS)==0",
                "detail": f"LHS-RHS = {sp.nsimplify(sp.simplify(L - R))}"}

    # inequality op in {<=, <}: normalize to 0 <= E  (E = R - L)
    E = sp.expand(R - L)
    used_syms = [s for s in (syms["x"], syms["y"]) if s in E.free_symbols]
    # (1) real Telperion Polya positivity certify
    try:
        sys.path.insert(0, __import__("os").path.expanduser("~/repos/Arda/telperion/src"))
        from telperion.certify import polya_certify
        polya_certify(E, used_syms, lift_max=2)
        return {"status": "reproduced", "check": "telperion.polya_certify",
                "detail": f"0 <= {E}  (Polya certificate)"}
    except ValueError as e:
        polya_detail = f"polya refused: {e}"
    except Exception as e:  # noqa: BLE001  (import/other) -> fall through to heuristic
        polya_detail = f"polya n/a: {e}"
    # (2) HEURISTIC numeric sampling fallback over the nonneg orthant.
    try:
        import random
        f = sp.lambdify(used_syms, E, "math") if used_syms else None
        worst = None
        pts = 400 if used_syms else 1
        for _ in range(pts):
            vals = [random.uniform(0, 12) for _ in used_syms]
            v = float(f(*vals)) if f else float(E)
            if worst is None or v < worst[0]:
                worst = (v, vals)
        if worst is not None and worst[0] < -1e-9:
            return {"status": "contradicted", "check": "numeric-sampling(HEURISTIC)",
                    "detail": f"negative at {dict(zip([str(s) for s in used_syms], worst[1]))}: {worst[0]:.4g}; {polya_detail}"}
        return {"status": "reproduced", "check": "numeric-sampling(HEURISTIC)",
                "detail": f"no violation in 400 nonneg samples (min {worst[0]:.4g}); {polya_detail}"}
    except Exception as e:  # noqa: BLE001
        return {"status": "out_of_fragment", "check": "-", "detail": f"sampling failed: {e}; {polya_detail}"}


def run_certify(candidate, show: int) -> None:
    from collections import Counter
    results = []
    for t in candidate:
        r = certify_candidate(t.goal_full or t.goal_excerpt)
        results.append((t, r))
    n = len(results)
    status = Counter(r["status"] for _, r in results)
    in_frag = status["reproduced"] + status["contradicted"]
    print("\n=== --certify : offline round-trip ('shaped' -> 'reproducible') ===")
    print(f"  candidates                 {n:4d}")
    print(f"  in-fragment (attempted)    {in_frag:4d}")
    print(f"    reproduced   (round-trip) {status['reproduced']:4d}")
    print(f"    CONTRADICTED (RED FLAG)   {status['contradicted']:4d}")
    print(f"  out-of-fragment (skipped)  {status['out_of_fragment']:4d}")
    frac = (status["reproduced"] / in_frag) if in_frag else 0.0
    print(f"  reproducible fraction (of in-fragment): {frac:.1%}")

    checks = Counter(r["check"] for _, r in results if r["status"] in ("reproduced", "contradicted"))
    if checks:
        print("  checks used:")
        for c, k in checks.most_common():
            print(f"    {k:4d}  {c}")

    contra = [(t, r) for t, r in results if r["status"] == "contradicted"]
    if contra:
        print(f"\n  RED FLAGS -- CONTRADICTED candidates ({len(contra)}):")
        for t, r in contra:
            print(f"    [{r['check']}] {t.file}:{t.name}")
            print(f"        goal: {t.goal_full[:120]}")
            print(f"        why : {r['detail']}")
    else:
        print("\n  RED FLAGS: none (no in-fragment candidate contradicted).")

    repro = [(t, r) for t, r in results if r["status"] == "reproduced"]
    if show and repro:
        print(f"\n  sample REPRODUCED (first {show}):")
        for t, r in repro[:show]:
            print(f"    [{r['check']}] {t.file}:{t.name}")
            print(f"        {t.goal_full[:110]}")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("roots", nargs="+")
    ap.add_argument("--json")
    ap.add_argument("--show", type=int, default=12, help="candidate examples to print")
    ap.add_argument("--certify", action="store_true",
                    help="offline round-trip: sympy/Polya-certify in-fragment candidates")
    args = ap.parse_args(argv)

    rep = Report()
    for root in args.roots:
        for p in sorted(Path(root).rglob("*.lean")):
            rep.scan_file(p)

    covered, candidate, structural, trivial = rep.buckets()
    total = len(rep.thms)
    print(f"scanned {total} theorems across {len(args.roots)} root(s)")
    print(f"  COVERED   (emitter-generated)          {len(covered):4d}")
    print(f"  CANDIDATE (hand-written, emitter-shaped) {len(candidate):4d}  <- proposal queue")
    print(f"  TRIVIAL   (all-numeric, norm_num/decide) {len(trivial):4d}  (filtered out)")
    print(f"  STRUCTURAL(hand-written, no emitter)    {len(structural):4d}")

    from collections import Counter
    print("\ncandidate shapes (what an existing emitter could regenerate):")
    for shape, n in Counter(t.shape for t in candidate).most_common():
        print(f"  {n:4d}  {shape:12s} -> {EMITTER_FOR.get(shape, '?')}")

    print(f"\nsample candidates (first {args.show}):")
    for t in candidate[:args.show]:
        print(f"  [{t.shape:11s}] {t.file}:{t.name}")
        print(f"              {t.goal_excerpt}")

    if args.certify:
        run_certify(candidate, args.show)

    if args.json:
        Path(args.json).write_text(json.dumps({
            "totals": {"covered": len(covered), "candidate": len(candidate),
                       "structural": len(structural)},
            "candidates": [t.__dict__ for t in candidate],
            "structural": [t.__dict__ for t in structural],
        }, indent=2))
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
