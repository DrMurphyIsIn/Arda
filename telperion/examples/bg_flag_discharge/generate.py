"""Generate the frozen BGFlagDischarge Lean module -- the route-(b) walk-count m_2 cut.

The mass-transport flag-LP dual is the antisymmetric edge-discharge potential w(d,e); with scalars
(b0,b1,b2) it gives a per-vertex inequality that telescopes over any tree to a certified lower bound
    m_2(T) >= b0 + b1*(2 - 2/n) + b2*m_1(T)          (see BG_WALK_COUNT_SUBPROBLEM.md, W8/W9).
Each emitted atom is a rational per-type inequality the Lean kernel re-checks by norm_num, tight at the
extremal caterpillar profile.  One finite level of a convergent hierarchy -- conjecture1_proved = False.

    python3 telperion/examples/bg_flag_discharge/generate.py         # (re)freeze the module
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from telperion.flag_discharge import FlagDischargeCertificate  # noqa: E402

DMAX = 7          # a=5 caterpillar: hub degree 7, arm-mid 2, leaf 1
DENOM = 720       # rationalization denominator for the LP dual
NAMESPACE = "BGFlagDischarge"


def _caterpillar_m1(a: int) -> Fr:
    """Exact m_1 of the length-2-arm caterpillar with a arms per spine vertex (long spine)."""
    sp = 50
    edges = []
    nid = sp
    for i in range(sp - 1):
        edges.append((i, i + 1))
    for i in range(sp):
        for _ in range(a):
            p = i
            for _ in range(2):
                edges.append((p, nid)); p = nid; nid += 1
    n = nid
    d = [0] * n
    adj = [[] for _ in range(n)]
    for x, y in edges:
        d[x] += 1; d[y] += 1; adj[x].append(y); adj[y].append(x)
    m1 = Fr(0)
    for v in range(n):
        m1 += sum(Fr(1, d[k]) for k in adj[v]) / d[v]
    return m1 / n


def certificate() -> FlagDischargeCertificate:
    cert = FlagDischargeCertificate.from_flag_lp(
        "bg_flag_discharge", dmax=DMAX, m1_target=_caterpillar_m1(DMAX - 2), denom=DENOM)
    assert cert.check(), "flag-discharge certificate failed exact check"
    return cert


def build() -> str:
    return certificate().lean_module(NAMESPACE)


def main() -> int:
    frozen = Path(__file__).resolve().parent / "frozen" / "BGFlagDischarge.lean"
    frozen.parent.mkdir(parents=True, exist_ok=True)
    frozen.write_text(build())
    print(f"froze {frozen.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
