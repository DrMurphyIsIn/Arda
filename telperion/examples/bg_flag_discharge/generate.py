"""Generate the frozen BGFlagDischarge Lean module -- the route-(b) walk-count m_2 cut.

The mass-transport flag-LP dual is the antisymmetric edge-discharge potential w(d,e); with scalars
(b0,b1,b2) it gives a per-vertex inequality that telescopes over any tree to a certified lower bound
    m_2(T) >= b0 + b1*(2 - 2/n) + b2*m_1(T)          (see BG_WALK_COUNT_SUBPROBLEM.md, W8/W9).
Each emitted atom is a rational per-type inequality the Lean kernel re-checks by norm_num, tight at the
extremal caterpillar profile.  One finite level of a convergent hierarchy -- conjecture1_proved = False.

The dual (B0,B1,B2,W below) was DERIVED offline by `FlagDischargeCertificate.from_flag_lp` (needs
numpy/scipy); it is FROZEN here as exact rationals so generation + manifest-verify need only the stdlib
(matching telperion's sympy-only CI).  To re-derive, run `from_flag_lp(dmax=7, m1_target=_caterpillar_m1(5),
denom=720)` and re-freeze.

    python3 telperion/examples/bg_flag_discharge/generate.py         # (re)freeze the module
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from telperion.flag_discharge import FlagDischargeCertificate  # noqa: E402

DMAX = 7
NAMESPACE = "BGFlagDischarge"

# frozen flag-LP dual (exact rationals; derived offline via from_flag_lp, denom=720, m1 = caterpillar a=5)
B0 = Fr(-1937, 3600)
B1 = Fr(13, 360)
B2 = Fr(1081, 720)
W = {
    (1, 3): Fr(9, 80), (1, 4): Fr(17, 90), (1, 5): Fr(29, 120), (1, 6): Fr(67, 240), (1, 7): Fr(221, 720),
    (2, 3): Fr(47, 720), (2, 4): Fr(31, 720), (2, 5): Fr(1, 40), (2, 6): Fr(1, 80), (2, 7): Fr(1, 180),
    (3, 4): Fr(19, 360), (3, 5): Fr(23, 360), (3, 6): Fr(13, 180), (3, 7): Fr(53, 720),
    (4, 5): Fr(29, 720), (4, 6): Fr(17, 360), (4, 7): Fr(37, 720),
    (5, 6): Fr(11, 360), (5, 7): Fr(1, 30), (6, 7): Fr(13, 720),
}


def _caterpillar_m1(a: int) -> Fr:
    """Exact m_1 of the length-2-arm caterpillar with a arms per spine vertex (long spine). stdlib only."""
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
    """Reconstruct the certificate from the frozen rational dual (stdlib only -- no LP solve)."""
    cert = FlagDischargeCertificate(name="bg_flag_discharge", dmax=DMAX, b0=B0, b1=B1, b2=B2, w=W)
    assert cert.check(), "frozen flag-discharge dual failed exact check"
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
