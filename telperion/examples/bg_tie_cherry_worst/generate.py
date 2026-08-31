"""Generate the BG tie-regime cherry-worst certificate (upper-bound campaign, kernel-gated).

    python examples/bg_tie_cherry_worst/generate.py           # write lean/BGTieCherryWorst.lean
    python examples/bg_tie_cherry_worst/generate.py --check    # drift check (no write)

The BG upper bound reduces to `ell(B) <= 0` for rooted branches, then (for UNIFORM hubs) to CHERRY-WORST: the
cherry is the worst uniform child in the tie regime, so `ell(hub of k children) <= ell(hub of k cherries) =
ell(B(k)) <= 0` (the last step is the PROVEN broom optimum).  See `docs/BG_TIE_REGIME_CAMPAIGN_20260831.md`.

Cherry-worst is `ell(k, cherry) - ell(k, B(j)) >= 0` for every broom-child `B(j)` (the branch envelope), which --
exponentiating by `11 = 2*5+1` to clear both `F* = log(621/64)/11` and the 11th root -- becomes the EXACT RATIONAL

    cherry_vs_broom_ratio(k, j) = exp(11*(ell(k,cherry) - ell(k,B(j))))  >  1.

It is UNIMODAL in `j` (min at the binding `j*(k)`), so `ratio(k, j*) > 1` certifies all `j` at that `k`.  It holds
for `k <= 20` (the tie regime; the tie `ell = 0` at `k = 5` sits deep inside), tightest at `k = 20`
(`ratio ~ 1.022`).  This example kernel-gates the finite family `1 < ratio(k, j*(k))` for `k in {2..20}` (`norm_num`,
exact rationals emitted by `TieCherryWorstCertificate`).

NOT the full upper bound: the slack regime `k >= 21` (soft bound), the mixed-hub convexity, and the non-envelope
Pareto cap remain (all TIE-FREE -- the `27*23` arithmetic is fully discharged by the broom optimum).
conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.tie_regime import TieCherryWorstCertificate  # noqa: E402

_CERT = TieCherryWorstCertificate(k_max=20)
NAMESPACE = "BGTieCherryWorst"
_OUT = Path(__file__).resolve().parent / "lean" / "BGTieCherryWorst.lean"


def build() -> str:
    assert _CERT.check(), "tie-regime cherry-worst certificate does not hold"
    head = (
        "/- BG tie-regime cherry-worst (upper-bound campaign, kernel-gated).\n"
        "   The upper bound reduces to CHERRY-WORST: the cherry is the worst uniform child, so ell(hub of k\n"
        "   children) <= ell(B(k)) <= 0 (broom optimum, proven). Cherry-worst = ell(k,cherry)-ell(k,B(j)) >= 0;\n"
        "   exponentiating by 11 (=2*5+1) clears F*=log(621/64)/11 and the 11th root, giving the exact rational\n"
        "   cherry_vs_broom_ratio(k,j) > 1, unimodal in j (min at j*), holding for k<=20 (tie k=5 deep inside,\n"
        "   tightest k=20 ratio~1.022). Atoms: 1 < ratio(k,j*(k)) for k in {2..20}. NOT the full bound (slack\n"
        "   regime k>=21 + mixed-hub convexity remain, all tie-free). conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module(NAMESPACE)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        cur = _OUT.read_text() if _OUT.exists() else ""
        if cur != src:
            print(f"DRIFT: {_OUT.relative_to(ROOT)} is stale -- re-run generate.py"); return 1
        print(f"ok: {_OUT.relative_to(ROOT)} matches"); return 0
    _OUT.parent.mkdir(parents=True, exist_ok=True)
    _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
