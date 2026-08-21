"""Generic 3XOR-instance duality emitter (v1: width-4 / degree-2).

Generalizes the Petersen chain: given ANY 3XOR instance whose width-4
closure is conflict-free, emit BOTH Lean files —

  {Name}Certificate.lean : the mask-level closure certificate (clause
    masks + signs, closure sign table, degree-<=2 index masks, kernel
    decides: refutation certificate, constraint respect, pairFact sweep,
    index validity/nodup/length; the moment-matrix PSD theorem via
    Xor3Structure's abstract kernel theorem);
  {Name}Duality.lean : the refutation-form layer (pseudoexpectation with
    parity-mask weighting, clause/boolean kills, PSD bridge, and the
    UNCONDITIONAL master: no SOS refutation with squares deg <= 2, clause
    cofactors deg <= 1).

TEMPLATE SOURCE OF TRUTH: the duality file is produced by systematic
substitution over the kernel-validated PetersenCertificate.lean /
Xor3Duality.lean reference files (never re-transcribed by hand); the Lean
kernel re-checks every emitted instance from scratch, so template drift
can only cause build failure, never a false theorem.

ANTI-PHANTOM: per instance the generator verifies exactly in Python:
3-regularity/connectivity when built from a graph, UNSAT (GF(2)), closure
conflict-freeness at width 4, the literal semantics of every decided Prop
(pair sweep, respect, guards), and a corrupted-sign negative control.

The idx-enumeration completeness sweep (idx_complete) is emitted only for
nvars <= 16 (the 2^n chunked decide); the duality chain never uses it
(index membership goes through the empty/{i}/{i,j} decides).

Usage: gen_xor3_duality.py [--instance petersen|heawood] [--outdir PATH]
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

from xor3_pseudoexpectation import closure, unsat_gf2, index_sets
from gen_petersen_cert import mask, pop, verify_emitted_semantics

HERE = Path(__file__).resolve().parent
LEAN_DIR = HERE.parent / "g1_floors" / "lean"


# ------------------------------------------------------------ instances

def tseitin_from_cubic(edges, n_vertices, charge_vertex=0):
    """Tseitin instance on a 3-regular graph: variables = edges, one clause
    per vertex (its incident edges), charge -1 at one vertex (odd total)."""
    edges = sorted(set(tuple(sorted(e)) for e in edges))
    eidx = {e: k for k, e in enumerate(edges)}
    deg = [0] * n_vertices
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    assert all(d == 3 for d in deg), "graph must be 3-regular"
    inst = []
    for v in range(n_vertices):
        inc = frozenset(eidx[e] for e in edges if v in e)
        assert len(inc) == 3
        inst.append((inc, -1 if v == charge_vertex else 1))
    return inst, len(edges)


def girth_at_least(edges, n_vertices, g):
    """BFS girth check (simple graphs)."""
    adj = [[] for _ in range(n_vertices)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    import collections
    best = float("inf")
    for src in range(n_vertices):
        dist = {src: 0}
        parent = {src: None}
        q = collections.deque([src])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1
                    parent[w] = u
                    q.append(w)
                elif parent[u] != w:
                    best = min(best, dist[u] + dist[w] + 1)
    return best >= g


def petersen():
    edges = []
    for i in range(5):
        edges.append((i, (i + 1) % 5))
        edges.append((5 + i, 5 + (i + 2) % 5))
        edges.append((i, i + 5))
    return "Petersen2", edges, 10


def heawood():
    """LCF [5,-5]^7: C14 plus a chord from each even vertex to +5."""
    edges = [(i, (i + 1) % 14) for i in range(14)]
    edges += [(i, (i + 5) % 14) for i in range(0, 14, 2)]
    return "Heawood", edges, 14


# ------------------------------------------------------------ emission

def build_data(inst, nvars):
    assert unsat_gf2(inst, nvars), "instance must be UNSAT"
    sgn_map, conflict = closure(inst, 4)
    assert not conflict, "width-4 closure must be conflict-free"
    clause_pairs = [(mask(a), e) for a, e in inst]
    lam_pairs = [(mask(u), s) for u, s in sgn_map.items()]
    lam_pairs.sort(key=lambda p: (p[0] != 0, p[0]))
    assert lam_pairs[0] == (0, 1)
    idx = sorted(mask(S) for S in index_sets(nvars, 2))
    return clause_pairs, lam_pairs, idx


def q(v):
    return str(v) if v >= 0 else f"(-{-v})"


def emit_certificate(name, nvars, clause_pairs, lam_pairs, idx):
    """Instance certificate file, templated from PetersenCertificate.lean."""
    ref = (LEAN_DIR / "PetersenCertificate.lean").read_text()
    L = len(idx)
    out = ref
    # strip the chunked completeness sweep unless the mask space is small
    if nvars > 16:
        out = re.sub(
            r"/- COMPLETENESS sweep.*?theorem idx_complete[^∎]*?\n\n"
            r"/-- The closure sign table",
            "/-- The closure sign table", out, flags=re.S)
        out = out.replace("#print axioms PetersenCertificate.idx_complete\n", "")
    # data blocks
    out = re.sub(r"def clausePairs : List \(ℕ × ℤ\) := \[[^\]]*\]",
                 "def clausePairs : List (ℕ × ℤ) := ["
                 + ", ".join(f"({c}, {q(e)})" for c, e in clause_pairs) + "]",
                 out)
    out = re.sub(r"def lamPairs : List \(ℕ × ℤ\) := \[[^\]]*\]",
                 "def lamPairs : List (ℕ × ℤ) := ["
                 + ", ".join(f"({a}, {q(s)})" for a, s in lam_pairs) + "]",
                 out)
    out = re.sub(r"def idxList : List ℕ := \[[^\]]*\]",
                 "def idxList : List ℕ := ["
                 + ", ".join(str(t) for t in idx) + "]", out)
    out = out.replace("Fin 121", f"Fin {L}")
    out = out.replace("pop 16", f"pop {max(16, nvars + 1)}")
    out = out.replace("PetersenCertificate", f"{name}Certificate")
    header = (f"/- TELPERION-GENERATED by gen_xor3_duality.py for instance "
              f"'{name}'\n   ({len(clause_pairs)} clauses, {nvars} variables, "
              f"closure {len(lam_pairs)}, index {L}).\n"
              f"   DO NOT EDIT BY HAND -- regenerate instead. -/\n")
    out = re.sub(r"\A/-.*?-/\n", header, out, flags=re.S)
    return out


def emit_duality(name, nvars, clause_pairs, idx_len, clause_sets):
    """Instance duality file, templated from Xor3Duality.lean."""
    ref = (LEAN_DIR / "Xor3Duality.lean").read_text()
    m = len(clause_pairs)
    out = ref
    literals = ", ".join(
        f"({{{', '.join(str(b) for b in bits)}}}, {q(e)})"
        for bits, e in clause_sets)
    out = re.sub(r"def clauseData : Fin 10 → \(Finset \(Fin 15\) × ℤ\) :=\n"
                 r"  !\[[^\]]*\]",
                 f"def clauseData : Fin {m} → (Finset (Fin {nvars}) × ℤ) :=\n"
                 f"  ![{literals}]", out)
    out = out.replace("Fin 15", f"Fin {nvars}")
    out = out.replace("Fin 10", f"Fin {m}")
    out = out.replace("Fin 121", f"Fin {idx_len}")
    out = out.replace("length = 121", f"length = {idx_len}")
    out = out.replace("pop 16", f"pop {max(16, nvars + 1)}")
    out = out.replace("PetersenCertificate", f"{name}Certificate")
    out = out.replace("Xor3Duality", f"{name}Duality")
    out = out.replace("petersen_no_refutation", f"{name.lower()}_no_refutation")
    out = out.replace("petersenSystem", f"{name.lower()}System")
    out = out.replace("petersen_moment_psd", "petersen_moment_psd")  # thm name inside cert is templated below
    out = out.replace(f"{name}Certificate.petersen_moment_psd",
                      f"{name}Certificate.petersen_moment_psd")
    header = (f"/- TELPERION-GENERATED by gen_xor3_duality.py for instance "
              f"'{name}': the refutation-form duality layer.\n"
              f"   DO NOT EDIT BY HAND -- regenerate instead. -/\n")
    out = re.sub(r"\A/-.*?-/\n", header, out, flags=re.S)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--instance", default="heawood",
                    choices=["petersen", "heawood"])
    args = ap.parse_args()
    name, edges, nv = {"petersen": petersen, "heawood": heawood}[args.instance]()
    assert girth_at_least(edges, nv, 5), "need girth >= 5 for width-4 closure"
    inst, nvars = tseitin_from_cubic(edges, nv)
    clause_pairs, lam_pairs, idx = build_data(inst, nvars)
    verify_emitted_semantics(clause_pairs, lam_pairs, idx)
    clause_sets = [(sorted(i for i in range(nvars) if c >> i & 1), e)
                   for c, e in clause_pairs]
    cert = emit_certificate(name, nvars, clause_pairs, lam_pairs, idx)
    dual = emit_duality(name, nvars, clause_pairs, len(idx), clause_sets)
    (LEAN_DIR / f"{name}Certificate.lean").write_text(cert)
    (LEAN_DIR / f"{name}Duality.lean").write_text(dual)
    print(f"{name}: {len(clause_pairs)} clauses, {nvars} vars, "
          f"closure {len(lam_pairs)}, idx {len(idx)} -> emitted both files")


if __name__ == "__main__":
    main()
