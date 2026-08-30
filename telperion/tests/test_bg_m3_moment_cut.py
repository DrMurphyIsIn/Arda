"""Route-(b) moment-degree-3 no-distant-competitor certificate: the ~7-arm caterpillar maximizes the
degree-3 walk-moment functional over structurally-distinct competitors.  Independently re-verifies the
radius-2 m_3 integrand by an exact rational matrix power (stdlib only).  conjecture1_proved = False."""
import importlib.util
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

_spec = importlib.util.spec_from_file_location(
    "bg_m3_gen", ROOT / "examples" / "bg_m3_moment_cut" / "generate.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


# ---- exact m_k via rational matrix power of P = A D^{-1} (N^{2k}_vv = (A D^{-1})^{2k}_vv) ----
def _mat_moment(n, edges, k):
    adj = [[] for _ in range(n)]
    deg = [0] * n
    for a, b in edges:
        adj[a].append(b); adj[b].append(a); deg[a] += 1; deg[b] += 1
    # P[i][j] = 1/deg[j] if i~j else 0
    P = [[Fr(0)] * n for _ in range(n)]
    for a, b in edges:
        P[a][b] = Fr(1, deg[b]); P[b][a] = Fr(1, deg[a])

    def matmul(X, Y):
        return [[sum(X[i][t] * Y[t][j] for t in range(n) if X[i][t]) for j in range(n)] for i in range(n)]

    M = [[Fr(1) if i == j else Fr(0) for j in range(n)] for i in range(n)]
    for _ in range(2 * k):
        M = matmul(M, P)
    return sum(M[i][i] for i in range(n)) / n, deg, adj


def _integrand_moment(n, edges, deg, adj):
    """m_3 via the example's radius-2 lhs_of_type, summed over vertices."""
    m3 = Fr(0)
    for v in range(n):
        nbrs = [(deg[a], sum(Fr(1, deg[c]) for c in adj[a])) for a in adj[v]]
        m3 += gen.lhs_of_type(deg[v], nbrs)[2]
    return m3 / n


def _small_caterpillar(spine, a, L=2):
    edges = []
    nid = spine
    for i in range(spine - 1):
        edges.append((i, i + 1))
    for i in range(spine):
        for _ in range(a):
            p = i
            for _ in range(L):
                edges.append((p, nid)); p = nid; nid += 1
    return nid, edges


def test_m3_integrand_matches_trace_exactly():
    # independent exact check: sum_v lhs_3(v)/n == Tr N^6 / n  (rational matrix power), several trees
    cases = [_small_caterpillar(4, 2, 2), _small_caterpillar(3, 3, 2),
             _small_caterpillar(3, 2, 3), (5, [(0, 1), (1, 2), (2, 3), (3, 4)])]
    for n, edges in cases:
        m3_mat, deg, adj = _mat_moment(n, edges, 3)
        m3_int = _integrand_moment(n, edges, deg, adj)
        assert m3_mat == m3_int, f"m3 mismatch: {m3_mat} != {m3_int}"


def test_argmax_atoms_hold_exactly():
    # every emitted atom is a strict rational inequality bound(comp) < bound(cat)
    for nm, lhs, rhs in gen.atoms():
        assert lhs < rhs, f"{nm}: {lhs} !< {rhs}"


def test_caterpillar_is_strict_argmax_over_competitors():
    bt = gen._bound(gen.TARGET)
    assert all(gen._bound(mv) < bt for mv in gen.COMPETITORS.values())


def test_bulk_moments_are_positive_and_ordered():
    # sanity: caterpillar bulk moments decrease with arm count near the optimum (m_3 monotone in a here)
    m3 = [gen.caterpillar_bulk(a)[2] for a in (5, 6, 7, 8, 9)]
    assert all(m3[i] > m3[i + 1] for i in range(len(m3) - 1))


def test_generate_is_idempotent():
    # the frozen Lean matches a fresh generation (drift gate)
    src = gen.build()
    assert src == gen._OUT.read_text()
