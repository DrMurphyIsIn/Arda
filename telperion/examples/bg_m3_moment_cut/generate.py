"""Generate the BG route-(b) moment-degree-3 no-distant-competitor certificate (kernel-gated).

    python examples/bg_m3_moment_cut/generate.py           # write lean/BGM3MomentCut.lean
    python examples/bg_m3_moment_cut/generate.py --check    # drift check (no write)

Route (b) bounds the matching free-energy density  F(T) = (1/2) integral log(1+u) dmu_N(u),
u = lambda^2, N = D^{-1/2} A D^{-1/2}, by the weighted walk moments  m_k(T) = (1/n) Tr N^{2k} =
integral u^k dmu_N.  For any degree-3 polynomial ENVELOPE  P_3(u) = c0 + c1 u + c2 u^2 + c3 u^3
with  P_3(u) >= (1/2) log(1+u)  on [0,1], every tree obeys  F(T) <= c1 m1 + c2 m2 + c3 m3 (+ c0).
So if the caterpillar MAXIMIZES that linear moment functional over a competitor set, then no competitor's
F exceeds  F(cat) + [c1 m1+c2 m2+c3 m3](cat) - F(cat)  -- the degree-3 "no distant competitor" step.

This example kernel-gates the ARGMAX:  the length-2-arm ~7-arm caterpillar strictly beats a set of
STRUCTURALLY DISTINCT competitors (the 2-regular path, the 3- and 4-regular trees, longer-arm L=3
caterpillars, and far-off arm counts a=3, a=10) under the moment functional  c1 m1 + c2 m2 + c3 m3.
The nearest-neighbour arm counts a=6, a=8 are the knife-edge handled separately by `bg_caterpillar_concavity`
(piece 2); this certificate covers the distant/structurally-different directions.

Moments are EXACT rationals computed (stdlib `fractions`) from the periodic bulk types via the per-vertex
radius-2 m_3 integrand  lhs_3 = C1r + T3/d + 2 S T2/d^2 + S^3/d^3  (derived by closed-6-walk / Dyck-path
enumeration + middle-vertex reassignment; sum_v lhs_k(v) = Tr N^{2k} VERIFIED to ~1e-16 vs the eigenvalue
ground truth on structured + 30 random trees).  The envelope coefficients (c1,c2,c3) are FROZEN exact
rationals (the tightest degree-3 upper envelope for the caterpillar, derived offline by LP; P_3 >= (1/2)log(1+u)
on [0,1] holds with min margin ~3.6e-4, interval-verified offline -- the enclosure-conditional turan/jensen
trust model).  Each emitted theorem is a rational inequality  bound(comp) < bound(cat)  the Lean kernel
re-checks by `norm_num`.  One finite level of a convergent hierarchy -- NOT a proof of Brualdi-Goldwasser
(the universal cut needs radius-2 mass-transport).  conjecture1_proved = False.
"""
import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NAMESPACE = "BGM3MomentCut"
_OUT = Path(__file__).resolve().parent / "lean" / "BGM3MomentCut.lean"

# FROZEN exact-rational degree-3 envelope coefficients (tightest upper envelope of (1/2)log(1+u) on [0,1]
# for the caterpillar; derived offline by LP, rationalized to den 5040).  c0 only shifts P_3 (cancels in the
# argmax comparison); c1,c2,c3 define the moment functional.  P_3(u) >= (1/2)log(1+u) on [0,1] (min margin
# ~3.6e-4, interval-verified offline).
C0, C1, C2, C3 = Fr(1, 504), Fr(1219, 2520), Fr(-947, 5040), Fr(1, 20)


def _rat(f: Fr) -> str:
    return f"(({f.numerator} : ℚ)/{f.denominator})" if f.denominator != 1 else f"(({f.numerator} : ℚ))"


def lhs_of_type(d, nbrs):
    """Exact (m1,m2,m3) per-vertex integrands for a radius-2 type: root degree d, neighbours a given as
    (d_a, S_a) with S_a = sum_{c~a} 1/d_c.  lhs_1=S/d, lhs_2=2S^2/d^2-Q/d^2 (radius-1); lhs_3 radius-2."""
    d = Fr(d)
    xa = [Fr(1, da) for da, _ in nbrs]
    Sa = [sa for _, sa in nbrs]
    S = sum(xa); Q = sum(x * x for x in xa)
    l1 = S / d
    l2 = 2 * S * S / (d * d) - Q / (d * d)
    T2 = sum((xa[i] ** 2) * (Sa[i] - 1 / d) for i in range(len(nbrs)))
    T3 = sum((xa[i] ** 3) * (Sa[i] - 1 / d) ** 2 for i in range(len(nbrs)))
    C1r = (1 / (d * d)) * sum((xa[i] ** 2) * (Sa[i] - 1 / d) * (S - xa[i]) for i in range(len(nbrs)))
    l3 = C1r + T3 / d + 2 * S * T2 / (d * d) + S ** 3 / d ** 3
    return l1, l2, l3


def caterpillar_bulk(a, L=2):
    """Exact bulk moment vector (m1,m2,m3) of the length-L-arm caterpillar with `a` arms per hub."""
    H = a + 2
    if L == 2:
        Sa_hub_spine = 2 * Fr(1, H) + a * Fr(1, 2)
        Sa_hub_arm = Fr(1, H) + Fr(1, 1)
        hub = (H, [(H, Sa_hub_spine)] * 2 + [(2, Sa_hub_arm)] * a)
        arm = (2, [(H, Sa_hub_spine), (1, Fr(1, 2))])
        leaf = (1, [(2, Sa_hub_arm)])
        parts = [(hub, 1), (arm, a), (leaf, a)]
    elif L == 3:
        Sa_hub_spine = 2 * Fr(1, H) + a * Fr(1, 2)
        Sa_mid1_mid2 = Fr(1, 2) + Fr(1, 1)
        hub = (H, [(H, Sa_hub_spine)] * 2 + [(2, Fr(1, H) + Fr(1, 2))] * a)
        mid1 = (2, [(H, Sa_hub_spine), (2, Sa_mid1_mid2)])
        mid2 = (2, [(2, Fr(1, H) + Fr(1, 2)), (1, Fr(1, 2))])
        leaf = (1, [(2, Sa_mid1_mid2)])
        parts = [(hub, 1), (mid1, a), (mid2, a), (leaf, a)]
    else:
        raise ValueError(L)
    tot = sum(w for _, w in parts)
    m = [Fr(0), Fr(0), Fr(0)]
    for (d, nbrs), w in parts:
        for i, v in enumerate(lhs_of_type(d, nbrs)):
            m[i] += w * v
    return tuple(x / tot for x in m)


def regular_bulk(d):
    """Exact moment vector of the infinite d-regular tree (all degrees d, every S_a = 1)."""
    return lhs_of_type(d, [(d, Fr(1))] * d)


TARGET = caterpillar_bulk(7)                       # the ~7-arm caterpillar
COMPETITORS = {                                    # structurally distinct / arm-count-distant
    "path_2reg": regular_bulk(2),
    "tree_3reg": regular_bulk(3),
    "tree_4reg": regular_bulk(4),
    "cat_a7_L3": caterpillar_bulk(7, 3),
    "cat_a5_L3": caterpillar_bulk(5, 3),
    "cat_a3_L2": caterpillar_bulk(3),
    "cat_a10_L2": caterpillar_bulk(10),
}


def _bound(mv):
    return C1 * mv[0] + C2 * mv[1] + C3 * mv[2]


def atoms():
    """(name, lhs, rhs) with the certified strict inequality lhs < rhs: bound(comp) < bound(cat)."""
    bt = _bound(TARGET)
    return [(f"bg_m3_cat_beats_{tag}", _bound(mv), bt) for tag, mv in COMPETITORS.items()]


def build() -> str:
    for nm, lhs, rhs in atoms():
        assert lhs < rhs, f"{nm}: argmax inequality fails ({lhs} < {rhs})"
    head = (
        "/- BG route-(b) moment-degree-3 no-distant-competitor certificate (kernel-gated).\n"
        "   F(T) = (1/2) integral log(1+u) dmu_N <= c1 m1 + c2 m2 + c3 m3 for the frozen degree-3 envelope\n"
        f"   P_3(u) = {C0} + {C1} u + ({C2}) u^2 + {C3} u^3 >= (1/2)log(1+u) on [0,1] (min margin ~3.6e-4,\n"
        "   interval-verified offline; turan/jensen enclosure model).  m_k = (1/n)Tr N^{2k}, exact rationals\n"
        "   from the verified radius-2 per-vertex integrand.  Atoms: the ~7-arm caterpillar strictly maximizes\n"
        "   c1 m1 + c2 m2 + c3 m3 over structurally-distinct competitors (2/3/4-regular trees, L=3-arm\n"
        "   caterpillars, arm counts 3 and 10) -- the distant-competitor directions.  The knife-edge a=6,a=8\n"
        "   are handled by bg_caterpillar_concavity (piece 2).  NOT a proof of Brualdi-Goldwasser (the\n"
        "   universal cut needs radius-2 mass-transport).  conjecture1_proved = False. -/\n"
        "import Mathlib\n\n"
        f"namespace {NAMESPACE}\n\n"
    )
    body = "\n".join(
        f"theorem {nm} : {_rat(lhs)} < {_rat(rhs)} := by norm_num" for nm, lhs, rhs in atoms()
    )
    return head + body + f"\n\nend {NAMESPACE}\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        cur = _OUT.read_text() if _OUT.exists() else ""
        if cur != src:
            print(f"DRIFT: {_OUT.relative_to(ROOT)} is stale -- re-run generate.py")
            return 1
        print(f"ok: {_OUT.relative_to(ROOT)} matches")
        return 0
    _OUT.parent.mkdir(parents=True, exist_ok=True)
    _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
