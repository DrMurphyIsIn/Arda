"""Generate the BG mixed-hub KKT certificate (upper-bound campaign, kernel-gated).

    python examples/bg_mixed_kkt/generate.py [--check]

The branch-induction upper bound needs `ell(hub) <= ell(B(k))` for MIXED hubs, `k <= 15` (the tie regime; the
slack regime `k >= 16` is gated separately by `bg_tie_slack`).  By the tangent of the concave `log` at the
all-cherry point, `ell(hub) - ell(B(k)) <= Sum_i (V(c_i) - V(cherry))` with `V(c) = ell(c) + lambda(k) x_c`,
`lambda(k) = 3(k+1)/(4k+3)`.  So the k-fold hub bound DECOUPLES into the per-child inequality `V(c) <= V(cherry)`
(the KKT condition), tie-free (a RELATIVE comparison; the `27*23` arithmetic stays in `ell(B(k)) <= 0`).
`MixedHubKKTCertificate` emits the rational atoms (frozen log-enclosures, concavity/turan trust model) proving
`V(c) < V(cherry)` for every broom child `B(2..8)` and `k` in `[2, 15]`.  See
`docs/BG_MIXED_KKT_20260831.md`.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.tie_regime import MixedHubKKTCertificate  # noqa: E402

_CERT = MixedHubKKTCertificate()
_OUT = Path(__file__).resolve().parent / "lean" / "BGMixedHubKKT.lean"


def build() -> str:
    assert _CERT.check(), "mixed-hub KKT certificate does not hold"
    head = (
        "/- BG mixed-hub KKT reduction (upper-bound campaign, kernel-gated).\n"
        "   For k<=15 (tie regime), the concave-log tangent at the all-cherry point gives ell(hub)-ell(B(k))\n"
        "   <= Sum_i (V(c_i)-V(cherry)), V(c)=ell(c)+lambda(k) x_c, lambda(k)=3(k+1)/(4k+3). So mixed<=B(k)\n"
        "   reduces to the per-child V(c)<V(cherry). Atoms (frozen log-enclosures): per broom child B(j) and\n"
        "   k in [2,15], 11 L(total_c)-11 L(3/2)-(|c|-2) L(621/64) < 11 lambda(k)(x_cherry-x_c). NOT the full\n"
        "   bound (broom optimum ell(B(k))<=0 + slack k>=16 are separate gates). conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module("BGMixedHubKKT")


def main() -> int:
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true"); a = ap.parse_args()
    src = build()
    if a.check:
        cur = _OUT.read_text() if _OUT.exists() else ""
        print("ok: matches" if cur == src else "DRIFT: re-run generate.py")
        return 0 if cur == src else 1
    _OUT.parent.mkdir(parents=True, exist_ok=True); _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}"); return 0


if __name__ == "__main__":
    sys.exit(main())
