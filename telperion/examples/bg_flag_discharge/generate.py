"""Generate the Brualdi-Goldwasser route-(b) walk-count m_2 cut certificate (kernel-gated).

    python examples/bg_flag_discharge/generate.py           # write lean/BGFlagDischarge.lean
    python examples/bg_flag_discharge/generate.py --check    # drift check (no write)

Route (b) bounds the matching free-energy growth rate rho* = lim_n max_T (per(L)/prod deg)^(1/n) by the
walk-moment functional.  The mass-transport flag-LP dual is an ANTISYMMETRIC edge-discharge potential
w(d,e) = -w(e,d); with scalars (b0,b1,b2) it gives a per-vertex inequality that telescopes over any tree
(sum_v sum_{a~v} w(d_v,d_a) = 0) plus the handshake (sum d = 2n-2) into a certified lower bound

    m_2(T) >= b0 + b1*(2 - 2/n) + b2*m_1(T),   m_k = (1/n) Tr N^{2k},  N = D^{-1/2} A D^{-1/2}.

The dual (B0,B1,B2,W below) was DERIVED OFFLINE by `FlagDischargeCertificate.from_flag_lp` (numpy/scipy);
it is FROZEN here as exact rationals so generation needs only the stdlib (sympy-only CI).  Each emitted
theorem is a rational per-type inequality the Lean kernel re-checks by `norm_num`, tight at the extremal
length-2-arm caterpillar.  One finite level of a convergent hierarchy -- NOT a proof of Brualdi-Goldwasser.
conjecture1_proved = False.  Full record: docs/BG_WALK_COUNT_SUBPROBLEM.md.
"""
import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from telperion.flag_discharge import FlagDischargeCertificate  # noqa: E402

DMAX = 7
NAMESPACE = "BGFlagDischarge"
_OUT = Path(__file__).resolve().parent / "lean" / "BGFlagDischarge.lean"

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
    """Exact m_1 of the length-2-arm caterpillar with a arms per spine vertex (long spine). stdlib only.
    (m1_target used offline to derive the frozen dual; kept for the test's valid-lower-bound check.)"""
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
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check: fail if lean/ is stale")
    args = ap.parse_args()
    src = build()
    if args.check:
        current = _OUT.read_text() if _OUT.exists() else ""
        if current != src:
            print(f"DRIFT: {_OUT.relative_to(ROOT)} is stale -- re-run generate.py")
            return 1
        print(f"ok: {_OUT.relative_to(ROOT)} matches the frozen dual")
        return 0
    _OUT.parent.mkdir(parents=True, exist_ok=True)
    _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
