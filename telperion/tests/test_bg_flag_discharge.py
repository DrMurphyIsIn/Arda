"""Route-(b) walk-count m_2 cut: the mass-transport flag-LP dual as an antisymmetric discharge potential,
kernel-gated per-type rational atoms.  conjecture1_proved = False."""
import importlib.util
import itertools
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion.flag_discharge import FlagDischargeCertificate, profile_moment_terms  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "bg_flag_gen", ROOT / "examples" / "bg_flag_discharge" / "generate.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def test_certificate_exact_check():
    cert = gen.certificate()
    # antisymmetric potential AND every degree-<=dmax per-type inequality holds, exactly
    assert cert.check()
    assert cert.antisymmetric()
    assert cert.worst_slack() >= 0
    # b0 is the exact infimum -> some type is tight
    assert cert.worst_slack() == 0


def test_potential_is_antisymmetric():
    cert = gen.certificate()
    for d in range(1, cert.dmax + 1):
        for e in range(1, cert.dmax + 1):
            assert cert.wval(d, e) == -cert.wval(e, d)
        assert cert.wval(d, d) == 0


def test_per_type_inequality_holds_exactly():
    cert = gen.certificate()
    # independent re-derivation of a handful of profiles from the exact moment terms
    for d, nbrs in [(1, (2,)), (2, (7, 1)), (3, (2, 2, 2)), (7, (2, 2, 2, 2, 2, 7, 7))]:
        x, q, lhs = profile_moment_terms(d, nbrs)
        disc = sum(cert.wval(d, e) for e in nbrs)
        assert lhs - (cert.b0 + cert.b1 * d + cert.b2 * x + disc) >= 0


def test_certified_bound_is_a_valid_lower_bound_at_caterpillar():
    cert = gen.certificate()
    m1 = gen._caterpillar_m1(cert.dmax - 2)
    # bulk certified bound m_2 >= b0 + 2 b1 + b2 m1  must be <= the caterpillar's actual m_2
    bound = cert.b0 + cert.b1 * 2 + cert.b2 * m1
    # caterpillar a=5 exact m_2
    a = cert.dmax - 2
    sp = 50; e = []; nid = sp
    for i in range(sp - 1):
        e.append((i, i + 1))
    for i in range(sp):
        for _ in range(a):
            p = i
            for _ in range(2):
                e.append((p, nid)); p = nid; nid += 1
    n = nid; d = [0] * n; adj = [[] for _ in range(n)]
    for x, y in e:
        d[x] += 1; d[y] += 1; adj[x].append(y); adj[y].append(x)
    m2 = Fr(0)
    for v in range(n):
        S = sum(Fr(1, d[k]) for k in adj[v]); Q = sum(Fr(1, d[k] ** 2) for k in adj[v])
        m2 += 2 * S * S / (d[v] * d[v]) - Q / (d[v] * d[v])
    m2 /= n
    assert bound <= m2                    # valid lower bound
    assert float(m2 - bound) < 5e-3       # tight to rationalization order


def test_emitted_atoms_are_rational_inequalities():
    src = gen.build()
    assert f"namespace {gen.NAMESPACE}" in src and src.rstrip().endswith(f"end {gen.NAMESPACE}")
    assert "conjecture1_proved = False" in src
    assert "Brualdi-Goldwasser" in src
    # every emitted theorem is a norm_num-checked rational inequality
    assert src.count(":= by norm_num") >= 4
    assert "≤" in src


def test_frozen_matches_generated():
    frozen = ROOT / "examples" / "bg_flag_discharge" / "frozen" / "BGFlagDischarge.lean"
    assert frozen.exists(), "run generate.py to freeze"
    assert frozen.read_text() == gen.build(), "frozen drift; re-run generate.py"
