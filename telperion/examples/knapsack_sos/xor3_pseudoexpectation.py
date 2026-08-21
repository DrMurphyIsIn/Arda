"""Random 3XOR SOS lower bound -- exact per-instance prototype (rung 1 for 3XOR).

Schoenebeck/Grigoriev construction in +-1 (Fourier) semantics: an instance is
a list of clauses (A, e) with A a 3-subset of [n], e in {+1,-1}, asserting
x_A := prod_{i in A} x_i = e.  The width-w CLOSURE is the BFS component of the
empty set in the graph on subsets of size <= w with edges S -> S xor A,
propagating signs sgn(S xor A) = e * sgn(S).  A sign CONFLICT during BFS is
exactly a width-w refutation of the instance.

Degree-d pseudoexpectation (w = 2d): E[x_U] = sgn(U) if U is in the closure,
else 0.  The moment matrix M[S,T] = E[x_{S xor T}] over |S|,|T| <= d.

STRUCTURE THEOREM (validated exactly here, per instance): indexing sets fall
into classes S ~ T iff (S xor T) in closure; when the closure is conflict-free
and sum-closed on the relevant widths, M is block-diagonal over classes and
each block is sigma sigma^T for the +-1 vector sigma_S = sgn(S xor R) -- so
M is PSD by construction.  This is the CORRECT structural picture for 3XOR:
NOT scheme-eigenvalue positivity (that is planted-clique/max-cut territory)
but GF(2) combinatorial consistency.  The asymptotic content (expansion =>
no width-eps*n refutation) is a combinatorial induction, not a positivity
certificate.

The money demo: an instance PROVABLY UNSAT (exact GF(2) Gaussian elimination)
whose width-2d closure is conflict-free ==> a fully certified per-instance
degree-2d SOS lower bound, with the PSD certificate being finite discrete
data (class partition + sign vectors).

TEETH (both directions):
  * a 4-clause contradiction with refutation width 3 is DETECTED at w >= 3
    and INVISIBLE at w = 2 (degree-1 matrix is the identity: PSD);
  * planted-satisfiable instances never conflict at any width and their
    moment matrices are genuine distributions (PSD sanity).

Everything in the verdict path is exact (integers / GF(2)); numeric eigvals
appear only as a redundant cross-check.

Usage: xor3_pseudoexpectation.py [--check]
"""
from __future__ import annotations

import argparse
import itertools
import random
import sys
from collections import deque


# ------------------------------------------------------------ instances

def random_instance(n: int, m: int, seed: int):
    rng = random.Random(seed)
    triples = list(itertools.combinations(range(n), 3))
    rng.shuffle(triples)
    return [(frozenset(t), rng.choice((1, -1))) for t in triples[:m]]


def planted_instance(n: int, m: int, seed: int):
    """Signs chosen consistent with a hidden +-1 assignment: satisfiable."""
    rng = random.Random(seed)
    hidden = [rng.choice((1, -1)) for _ in range(n)]
    triples = list(itertools.combinations(range(n), 3))
    rng.shuffle(triples)
    out = []
    for t in triples[:m]:
        e = hidden[t[0]] * hidden[t[1]] * hidden[t[2]]
        out.append((frozenset(t), e))
    return out


def unsat_gf2(instance, n: int) -> bool:
    """Exact GF(2) Gaussian elimination: True iff the system is UNSAT."""
    rows = []
    for aset, e in instance:
        vec = 0
        for i in aset:
            vec |= 1 << i
        rhs = 0 if e == 1 else 1
        rows.append((vec, rhs))
    pivots = {}
    for vec, rhs in rows:
        while vec:
            p = vec.bit_length() - 1
            if p in pivots:
                pv, pr = pivots[p]
                vec ^= pv
                rhs ^= pr
            else:
                pivots[p] = (vec, rhs)
                vec = 0
                rhs = 0
                break
        else:
            if rhs == 1:
                return True
    return False


# ------------------------------------------------------------ closure

def closure(instance, w: int):
    """Width-w BFS closure of the empty set. Returns (sgn, conflict)."""
    sgn = {frozenset(): 1}
    queue = deque([frozenset()])
    while queue:
        S = queue.popleft()
        for aset, e in instance:
            T = S ^ aset
            if len(T) > w:
                continue
            val = e * sgn[S]
            if T in sgn:
                if sgn[T] != val:
                    return sgn, True
            else:
                sgn[T] = val
                queue.append(T)
    return sgn, False


# ------------------------------------------------------------ moment matrix

def index_sets(n: int, d: int):
    out = []
    for i in range(d + 1):
        out.extend(frozenset(S) for S in itertools.combinations(range(n), i))
    return out


def moment_matrix(sgn, idx):
    return [[sgn.get(S ^ T, 0) for T in idx] for S in idx]


def class_partition(sgn, idx):
    """Partition index sets into derivability classes; None if not transitive."""
    reps = []
    assign = {}
    for S in idx:
        for r, R in enumerate(reps):
            if (S ^ R) in sgn:
                assign[S] = r
                break
        else:
            assign[S] = len(reps)
            reps.append(S)
    # exact transitivity check: same class <=> difference in closure
    for S in idx:
        for T in idx:
            if (assign[S] == assign[T]) != ((S ^ T) in sgn):
                return None, None, None
    sigma = {S: sgn[S ^ reps[assign[S]]] for S in idx}
    return reps, assign, sigma


def verify_block_rank_one(sgn, idx) -> tuple[bool, int]:
    """Exact: M[S,T] == sigma_S sigma_T [same class] entrywise. PSD certificate."""
    reps, assign, sigma = class_partition(sgn, idx)
    if reps is None:
        return False, -1
    for S in idx:
        for T in idx:
            want = sigma[S] * sigma[T] if assign[S] == assign[T] else 0
            if sgn.get(S ^ T, 0) != want:
                return False, -1
    return True, len(reps)


def verify_constraint_respect(instance, sgn, w: int) -> bool:
    """E[x_C x_S] = e_C E[x_S] whenever both sides' sets are within width."""
    for S in list(sgn):
        for aset, e in instance:
            T = S ^ aset
            if len(T) <= w:
                if sgn.get(T, 0) != e * sgn.get(S, 0):
                    return False
    return True


# ------------------------------------------------------------ validations

def validate_planted() -> None:
    for seed in range(3):
        n, m = 10, 14
        inst = planted_instance(n, m, seed)
        assert not unsat_gf2(inst, n), "planted instance must be SAT"
        sgn, conflict = closure(inst, 6)
        assert not conflict, "planted instance produced a conflict"
        idx = index_sets(n, 3)
        ok, ncls = verify_block_rank_one(sgn, idx)
        assert ok, "planted: block rank-1 structure failed"
    print("PASS planted (SAT) instances: conflict-free closure, exact block "
          "rank-1 PSD certificate at d=3")


def validate_teeth() -> None:
    # width-3 contradiction: {1,2,3},{1,2,4},{5,6,3},{5,6,4} with sign product -1
    inst = [(frozenset({1, 2, 3}), 1), (frozenset({1, 2, 4}), 1),
            (frozenset({5, 6, 3}), 1), (frozenset({5, 6, 4}), -1)]
    n = 7
    assert unsat_gf2(inst, n), "teeth instance must be UNSAT"
    _, c3 = closure(inst, 3)
    assert c3, "width-3 refutation must be found at w=3"
    sgn2, c2 = closure(inst, 2)
    assert not c2, "w=2 must NOT see the refutation"
    idx1 = index_sets(n, 1)
    M = moment_matrix(sgn2, idx1)
    assert all(M[i][j] == (1 if i == j else 0)
               for i in range(len(idx1)) for j in range(len(idx1))), \
        "d=1 moment matrix must be the identity"
    print("PASS teeth: UNSAT instance with refutation width exactly 3 -- "
          "detected at w=3, invisible at w=2 (M_1 = identity, PSD)")


def petersen_tseitin():
    """Tseitin contradiction on the Petersen graph: the canonical money
    instance. 3-regular, girth 5 => no proper clause-subset has edge-boundary
    <= 5, so the refutation width is forced up; odd total charge => UNSAT.
    Variables = the 15 edges; one 3XOR clause per vertex; charge -1 at v0."""
    edges = []
    for i in range(5):
        edges.append(tuple(sorted((i, (i + 1) % 5))))
        edges.append(tuple(sorted((5 + i, 5 + (i + 2) % 5))))
        edges.append(tuple(sorted((i, i + 5))))
    edges = sorted(set(edges))
    eidx = {e: k for k, e in enumerate(edges)}
    inst = []
    for v in range(10):
        inc = frozenset(eidx[e] for e in edges if v in e)
        inst.append((inc, -1 if v == 0 else 1))
    return inst, len(edges)


def validate_money() -> None:
    inst, n = petersen_tseitin()
    assert unsat_gf2(inst, n), "Petersen Tseitin must be UNSAT"
    widths = {}
    for w in (3, 4, 5, 6):
        _, conflict = closure(inst, w)
        widths[w] = conflict
    assert widths == {3: False, 4: False, 5: False, 6: True}, widths
    sgn, _ = closure(inst, 4)
    idx = index_sets(n, 2)
    ok, ncls = verify_block_rank_one(sgn, idx)
    assert ok, "Petersen: block rank-1 structure failed"
    assert verify_constraint_respect(inst, sgn, 4), "constraint respect failed"
    # redundant numeric cross-check of PSD
    import numpy as np
    M = np.array(moment_matrix(sgn, idx), dtype=float)
    ev = float(np.min(np.linalg.eigvalsh(M)))
    assert ev > -1e-9, ev
    print(f"PASS money demo (Petersen Tseitin, deterministic): 15 edge "
          f"variables, 10 clauses, PROVABLY UNSAT (exact GF(2)); refutation "
          f"width EXACTLY 6 (conflict-free at w=3,4,5; conflict at 6, "
          f"matching the girth-5 boundary argument); {len(idx)}x{len(idx)} "
          f"moment matrix = exact block-rank-1 over {ncls} classes ==> "
          f"certified degree-4 SOS lower bound (min eig cross-check {ev:.2e})")


def validate_negative_control() -> None:
    """Corrupt one sign in a verified closure: structure check must fail."""
    inst, n = petersen_tseitin()
    sgn, _ = closure(inst, 4)
    idx = index_sets(n, 2)
    bad = dict(sgn)
    key = next(S for S in bad if len(S) == 3)
    bad[key] = -bad[key]
    ok, _ = verify_block_rank_one(bad, idx)
    assert not ok, "corrupted sign not detected"
    print("PASS negative control: corrupted closure sign breaks the exact "
          "rank-1 certificate check")


def report_structure() -> None:
    print()
    print("=== 3XOR structural findings (corrects the earlier W2 framing) ===")
    print("The 3XOR moment matrix is NOT a scheme-eigenvalue object: it is")
    print("block-diagonal over GF(2) derivability classes with +-1 rank-1")
    print("blocks. PSD == combinatorial consistency (no width-2d refutation).")
    print("Lean target therefore: the generic structure theorem")
    print("  conflict-free width-2d closure ==> M_d = direct sum of sigma*sigma^T ==> PSD,")
    print("with per-instance certificates = (class partition, sign vector),")
    print("emitter-shaped and finite. The asymptotic layer (expansion ==> no")
    print("width-eps*n refutation, whp for random instances) is combinatorial")
    print("induction + probability -- honest-conditional assembly territory,")
    print("NOT holonomic positivity. Scheme-eigenvalue/W2 machinery belongs")
    print("to planted clique / Laurent max-cut, not here.")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    validate_planted()
    validate_teeth()
    validate_money()
    validate_negative_control()
    report_structure()
    print()
    print("ALL GREEN: 3XOR per-instance pseudoexpectation machinery verified "
          "exactly.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
