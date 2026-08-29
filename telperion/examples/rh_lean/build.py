"""Assemble the RH lake library from the frozen emitted Lean + transcendental
samples, so CI `lake build` actually KERNEL-CHECKS the whole RH/transcendental
line (turan/jensen/toeplitz/newton hyperbolicity + exp/log brackets).

Frozen files stay the source of truth; this copies them into RH/<Module>.lean
(module path = namespace-independent) and writes the library root.  Transcendental
certificates without an example (LogBound) get a small generated sample module.

    python3 examples/rh_lean/build.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXAMPLES = HERE.parent
sys.path.insert(0, str(EXAMPLES.parent / "src"))

from fractions import Fraction as Fr  # noqa: E402

from telperion import (  # noqa: E402
    GammaHalfBracketCertificate, HankelJensenCertificate, LogBoundCertificate,
    PiBracketCertificate, QuarticJensenCertificate, RobinCertificate,
    SqrtBracketCertificate, TightRobinCertificate, ZetaBoundCertificate,
)

# gamma_k = k! a_k enclosures at 1e-30 (tight enough for the quartic Delta4's
# delicate cancellation), k=0..5 -> certifies quartic hyperbolicity shifts n=0,1.
_QUARTIC_GAMMAS = (
    ("99424155637662821982554747937/200000000000000000000000000000", "248560389094157054956386869843/500000000000000000000000000000"),
    ("1435746519696589845953117281/125000000000000000000000000000", "11485972157572718767624938249/1000000000000000000000000000000"),
    ("123452018070318006890345791/500000000000000000000000000000", "246904036140636013780691583/1000000000000000000000000000000"),
    ("624266611039145304003569/125000000000000000000000000000", "4994132888313162432028553/1000000000000000000000000000000"),
    ("47906718616129646096703/500000000000000000000000000000", "95813437232259292193407/1000000000000000000000000000000"),
    ("1753923091213315303489/1000000000000000000000000000000", "175392309121331530349/100000000000000000000000000000"),
)

# frozen emitted Lean  ->  RH library module
FROZEN = {
    "Turan": "turan_xi/frozen/RiemannTuran.lean",
    "Jensen": "jensen_xi/frozen/CubicJensen.lean",
    "Toeplitz": "toeplitz_xi/frozen/ToeplitzXi.lean",
    "Newton": "newton_xi/frozen/NewtonXi.lean",
    "ExpBracket": "exp_bracket/frozen/ExpBracket.lean",
    "BGRhoBSqrt": "bg_rhob_sqrt/frozen/BGRhoBSqrt.lean",  # sqrt_bracket regenerating BG's e2 sqrt 2 crux
    "BGLogEnclosures": "bg_log_enclosures/frozen/BGLogEnclosures.lean",  # TightLog regenerating BG's sweep log(3/2),log(4/3)
    "BGOmegaEnclosure": "bg_omega_enclosure/frozen/BGOmegaEnclosure.lean",  # Taylor-log+d9 regenerating BG's omega enclosure
    "BGGateStrictness": "bg_gate_strictness/frozen/BGGateStrictness.lean",  # 23-gate-strictness deficit certs (exact bignum divisibility)
    "BGParityLaw": "bg_parity_law/frozen/BGParityLaw.lean",  # per-n extremality parity law: exact extremal Phi^11 <1 (=1 @n=11), n<=14
    "BGCollectiveCancellation": "bg_collective_cancellation/frozen/BGCollectiveCancellation.lean",  # claim-1 obstruction: 2 per-vertex factors >1, product=1
}


def _logbound_module() -> str:
    # a handful of in-kernel Real.log brackets (transcendental skill, no example)
    samples = [("log_two", 2, 1), ("log_three_halves", 3, 2), ("log_ten", 10, 1)]
    body = "\n\n".join(
        LogBoundCertificate(name=nm, n=n, d=d).lean().rstrip() for nm, n, d in samples)
    return ("/- Generated transcendental samples (LogBoundCertificate). -/\n"
            "import Mathlib\n\nnamespace LogBound\n\n" + body + "\n\nend LogBound\n")


def _pi_module() -> str:
    thm = PiBracketCertificate(name="pi_bracket").lean().rstrip()
    return ("/- Generated transcendental sample (PiBracketCertificate). -/\n"
            "import Mathlib\n\nnamespace PiBracket\n\n" + thm + "\n\nend PiBracket\n")


def _sqrt_module() -> str:
    samples = [("sqrt_two", 2, 1), ("sqrt_three", 3, 1), ("sqrt_ten", 10, 1)]
    body = "\n\n".join(
        SqrtBracketCertificate.build(nm, qn, qd).lean().rstrip() for nm, qn, qd in samples)
    return ("/- Generated transcendental samples (SqrtBracketCertificate). -/\n"
            "import Mathlib\n\nnamespace SqrtBracket\n\n" + body + "\n\nend SqrtBracket\n")


def _zeta_module() -> str:
    # Hand-written zeta-numerics lemmas, landed via CI iteration in the sandbox
    # (examples/mathlib_probe) and promoted here to the kernel-gated library.
    return r'''/- zeta-numerics, landed in-kernel against Mathlib v4.32.0.
   zeta(2) bounds (from pi^2/6) and zeta(3) > 9/8 (Apery's constant, NO closed
   form) via the Dirichlet series zeta_eq_tsum_one_div_nat_cpow + a partial sum. -/
import Mathlib
open scoped Real

namespace ZetaNumerics

theorem riemannZeta_two_re_bounds :
    (3 : ℝ) / 2 < (riemannZeta 2).re ∧ (riemannZeta 2).re < 8 / 3 := by
  have h : riemannZeta 2 = ((π ^ 2 / 6 : ℝ) : ℂ) := by
    rw [riemannZeta_two]; push_cast; ring
  rw [h, Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · nlinarith [Real.pi_gt_three, Real.pi_pos]
  · nlinarith [Real.pi_lt_four, Real.pi_pos]

/-- zeta(3) as a real Dirichlet series (each complex term is a nonneg real cast). -/
theorem riemannZeta_three_eq_ofReal :
    riemannZeta 3 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]
  push_cast; ring

/-- Apery's constant zeta(3) exceeds 9/8 (no closed form; first 3 series terms). -/
theorem riemannZeta_three_re_ge : (9 : ℝ) / 8 ≤ (riemannZeta 3).re := by
  rw [riemannZeta_three_eq_ofReal, Complex.ofReal_re]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h3 : (∑ n ∈ Finset.range 3, 1 / (n : ℝ) ^ 3) = 9 / 8 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  calc (9 : ℝ) / 8 = ∑ n ∈ Finset.range 3, 1 / (n : ℝ) ^ 3 := h3.symm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 3 :=
        hsum.sum_le_tsum (Finset.range 3) (fun i _ => by positivity)

/-- zeta(4) bounds from the exact value pi^4/90 and 3 < pi < 4. -/
theorem riemannZeta_four_re_bounds :
    (9 : ℝ) / 10 < (riemannZeta 4).re ∧ (riemannZeta 4).re < 128 / 45 := by
  have h : riemannZeta 4 = ((π ^ 4 / 90 : ℝ) : ℂ) := by
    rw [riemannZeta_four]; push_cast; ring
  rw [h, Complex.ofReal_re]
  have h9 : (9 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have h16 : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hp : (0 : ℝ) < π ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [h9, hp]
  · nlinarith [h16, hp]

/-- Apery's constant zeta(3) < 5/4 (tight two-sided with zeta(3) >= 9/8): the
    Dirichlet-series tail 1/(n+3)^3 <= g n - g(n+1) telescopes to g 0 = 1/12. -/
theorem riemannZeta_three_re_le : (riemannZeta 3).re < 5 / 4 := by
  rw [riemannZeta_three_eq_ofReal, Complex.ofReal_re]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsplit := hf.sum_add_tsum_nat_add 3
  have h3 : (∑ i ∈ Finset.range 3, 1 / (i : ℝ) ^ 3) = 9 / 8 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  set g : ℕ → ℝ := fun i => 1 / (2 * ((i : ℝ) + 2) * ((i : ℝ) + 3)) with hg
  have hterm : ∀ i : ℕ, (1 / (((i + 3 : ℕ)) : ℝ) ^ 3) ≤ g i - g (i + 1) := by
    intro i
    have h2 : ((i : ℝ) + 2) ≠ 0 := by positivity
    have h3' : ((i : ℝ) + 3) ≠ 0 := by positivity
    have h4 : ((i : ℝ) + 4) ≠ 0 := by positivity
    have e : g i - g (i + 1) = 1 / (((i : ℝ) + 2) * ((i : ℝ) + 3) * ((i : ℝ) + 4)) := by
      simp only [hg]; push_cast; field_simp; ring
    have hfi : (1 / (((i + 3 : ℕ)) : ℝ) ^ 3) = 1 / ((i : ℝ) + 3) ^ 3 := by push_cast; ring
    rw [hfi, e]
    apply one_div_le_one_div_of_le (by positivity)
    have hid : ((i : ℝ) + 3) ^ 3 - (((i : ℝ) + 2) * ((i : ℝ) + 3) * ((i : ℝ) + 4)) = (i : ℝ) + 3 := by
      ring
    nlinarith [hid, (by positivity : (0 : ℝ) ≤ (i : ℝ) + 3)]
  have htailsum : Summable (fun i : ℕ => 1 / (((i + 3 : ℕ)) : ℝ) ^ 3) :=
    (summable_nat_add_iff 3).mpr hf
  have htail : (∑' i : ℕ, 1 / (((i + 3 : ℕ)) : ℝ) ^ 3) ≤ 1 / 12 := by
    apply htailsum.tsum_le_of_sum_range_le
    intro N
    calc ∑ i ∈ Finset.range N, 1 / (((i + 3 : ℕ)) : ℝ) ^ 3
        ≤ ∑ i ∈ Finset.range N, (g i - g (i + 1)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = g 0 - g N := Finset.sum_range_sub' g N
      _ ≤ 1 / 12 := by
          have hg0 : g 0 = 1 / 12 := by simp only [hg]; norm_num
          have hgN : (0 : ℝ) ≤ g N := by simp only [hg]; positivity
          rw [hg0]; linarith [hgN]
  rw [← hsplit, h3]
  linarith [htail]

end ZetaNumerics
'''


def _zeta_emitter_module() -> str:
    # ZetaBoundCertificate emitter: new kernel-verified zeta(k) two-sided bounds
    # for odd/higher k (no closed form), demonstrating the reusable emitter beyond
    # the bespoke ZetaNumerics hand-proofs.
    insts = [
        ZetaBoundCertificate(name="zeta_five_bound", k=5, M=4),
        ZetaBoundCertificate(name="zeta_six_bound", k=6, M=4),
        ZetaBoundCertificate(name="zeta_seven_bound", k=7, M=4),
    ]
    body = "\n\n".join(c.lean().rstrip() for c in insts)
    return ("/- Generated by ZetaBoundCertificate: two-sided zeta(k) bounds, k>=2,\n"
            "   via the Dirichlet series + square-telescoping tail (any k, any precision). -/\n"
            "import Mathlib\nopen scoped Real\n\nnamespace ZetaEmitter\n\n" + body
            + "\n\nend ZetaEmitter\n")


def _quartic_module() -> str:
    enc = tuple((Fr(lo), Fr(hi)) for lo, hi in _QUARTIC_GAMMAS)
    body = QuarticJensenCertificate(name="quartic_jensen_xi", enclosures=enc).lean().rstrip()
    return ("/- Degree-4 Jensen-Polya hyperbolicity of xi (QuarticJensenCertificate via\n"
            "   the general WorstCornerCertificate): J^{4,n} all-real <=> Delta4>0 & P<0 & D<0,\n"
            "   for shifts n=0,1 over gamma_k=k!a_k enclosures. RH-necessary, finite. -/\n"
            "import Mathlib\nopen scoped Real\n\nnamespace QuarticJensen\n\n" + body
            + "\n\nend QuarticJensen\n")


def _hankel_module() -> str:
    """Degree-5 Jensen hyperbolicity via the general Hermite/Hankel-minor emitter
    (the uniform any-degree criterion; d<=4 have short discriminant forms, d>=5 do
    not).  Same gamma_k=k!a_k enclosures as the quartic; shift n=0 needs g_0..g_5."""
    enc = tuple((Fr(lo), Fr(hi)) for lo, hi in _QUARTIC_GAMMAS)
    body = HankelJensenCertificate(name="hankel_jensen_xi", enclosures=enc, degree=5).lean().rstrip()
    return ("/- Degree-5 Jensen-Polya hyperbolicity of xi via the Hermite/Hankel-minor\n"
            "   criterion (HankelJensenCertificate): J^{5,0} STRICTLY hyperbolic <=> the\n"
            "   Hermite form is PD <=> every leading Hankel minor Dtau_r > 0, r=2..5.\n"
            "   Uniform any-degree generalization of turan/cubic/quartic. RH-necessary,\n"
            "   finite shift, enclosure-conditional. -/\n"
            "import Mathlib\nopen scoped Real\n\nnamespace HankelJensen\n\n" + body
            + "\n\nend HankelJensen\n")


def _robin_module() -> str:
    """Robin's criterion (RH-EQUIVALENT, arithmetic): sigma(n) < e^gamma n loglog n,
    UNCONDITIONAL (both brackets discharged in-kernel) for a few comfortable n.  A
    genuinely different angle from the analytic hyperbolicity ladder."""
    from fractions import Fraction as Fr2
    ns = (5041, 5042, 8192, 65537)
    body = "\n\n".join(
        RobinCertificate.from_gamma_lower(n=n, gamma_lo=Fr2(1, 2)).lean_unconditional().rstrip()
        for n in ns)
    # RH-TIGHT SUPERABUNDANT regime: every superabundant number in (5040, 2*10^6] (there are
    # exactly 13), all beyond the comfortable gamma>1/2 bound -- tight eulerMascheroniSeq gamma
    # + tight taylor_log loglog.  These are the numbers the SA reduction (D3) must cover.
    SA = (10080, 15120, 25200, 27720, 55440, 110880, 166320,
          277200, 332640, 554400, 665280, 720720, 1441440)
    body += "\n\n" + "\n\n".join(
        TightRobinCertificate.for_superabundant(n).lean().rstrip() for n in SA)
    return ("/- Robin's criterion for RH (Robin 1984), UNCONDITIONAL in-kernel instances:\n"
            "   sigma(n) < e^gamma * n * log log n for n in {5041,5042,8192,65537} (comfortable)\n"
            "   and for ALL 13 SUPERABUNDANT numbers in (5040, 2*10^6] (RH-tight regime).  RH <=>\n"
            "   this holds for all n >= 5041; a single violator disproves RH -- so each is a finite\n"
            "   check consistent with (never a proof of) RH.  Comfortable n: e^gamma from\n"
            "   Real.one_half_lt_eulerMascheroniConstant + Taylor exp, loglog from log-2 d9.\n"
            "   Superabundant n: tight e^gamma from eulerMascheroniSeq, tight loglog from taylor_log.\n"
            "   See ROBIN_REDUCTION_D3.md for the reduction scope (this does NOT prove all n <= X). -/\n"
            "import Mathlib\nopen scoped Real\n\nnamespace Robin\n\n" + body
            + "\n\nend Robin\n")


def _nicolas_module() -> str:
    """D4: the Nicolas => Robin bridge  phi(n) * sigma(n) < n^2  (sigma = sum of divisors).
    This elementary inequality (UNCONDITIONALLY true for n > 1) is exactly sigma(n)/n <
    n/phi(n), the connector that makes Nicolas's RH-equivalent criterion imply Robin's
    (Nicolas 1983).  Finite kernel instances at primorials 6, 30, 210.  NOTE: this bridge is
    NOT itself RH-equivalent (it always holds); the RH content lives in Nicolas's
    n/phi(n) < e^gamma loglog n (which needs the tight transcendental brackets), and the
    GENERAL phi*sigma<n^2 for all n needs the multiplicative product assembly (D2: medium)."""
    body = "\n\n".join(
        f"theorem nicolas_robin_bridge_{n} :\n"
        f"    Nat.totient {n} * (∑ d ∈ Nat.divisors {n}, d) < {n} ^ 2 := by decide"
        for n in (6, 30, 210))
    return ("/- D4: Nicolas => Robin bridge  phi(n) * sigma(n) < n^2  (= sigma(n)/n < n/phi(n)),\n"
            "   the elementary connector making Nicolas's RH-equivalent criterion imply Robin's.\n"
            "   Unconditionally true; finite instances at primorials. NOT itself RH-equivalent,\n"
            "   proves nothing about RH.  See ROBIN_RH_MAP.md (equivalences) / ROBIN_REDUCTION_D3.md. -/\n"
            "import Mathlib\n\nnamespace NicolasBridge\n\n" + body + "\n\nend NicolasBridge\n")


def _robin_reduction_module() -> str:
    """The G-monotonicity reduction lemma (D3): the elementary heart of 'the least Robin
    counterexample is superabundant' (Akbary-Friggstad 2009).  Reduction lemma only --
    proves nothing about RH."""
    return (
        "/- D3: G-monotonicity reduction lemma. If sigma(m)/m >= sigma(n)/n and log log m <=\n"
        "   log log n (as when m <= n), then G(n)=sigma(n)/(n loglog n) <= G(m).  A Robin\n"
        "   violation at n forces one at the abundancy-record m -- so the least Robin\n"
        "   counterexample is superabundant.  Reduction lemma only; proves nothing about RH. -/\n"
        "import Mathlib\nopen scoped Real\n\nnamespace RobinReduction\n\n"
        "theorem robin_G_monotone\n"
        "    {sm sn m n : ℝ} (hsm : 0 ≤ sm / m)\n"
        "    (habund : sn / n ≤ sm / m)\n"
        "    (hLm : 0 < Real.log (Real.log m))\n"
        "    (hLmn : Real.log (Real.log m) ≤ Real.log (Real.log n)) :\n"
        "    sn / (n * Real.log (Real.log n)) ≤ sm / (m * Real.log (Real.log m)) := by\n"
        "  rw [← div_div, ← div_div]\n"
        "  gcongr\n\n"
        "end RobinReduction\n")


def _gammahalf_module() -> str:
    thm = GammaHalfBracketCertificate(name="gamma_half_bracket").lean().rstrip()
    return ("/- Generated: a COMPLETED in-kernel bracket of the deep transcendental\n"
            "   Gamma(1/2) = sqrt(pi) (GammaHalfBracketCertificate). -/\n"
            "import Mathlib\n\nnamespace GammaHalf\n\n" + thm + "\n\nend GammaHalf\n")


def modules() -> dict:
    out = {}
    for mod, rel in FROZEN.items():
        out[mod] = (EXAMPLES / rel).read_text()
    out["LogBound"] = _logbound_module()
    out["SqrtBracket"] = _sqrt_module()
    out["PiBracket"] = _pi_module()          # now uses confirmed Real.pi_gt_three / pi_lt_four
    out["GammaHalf"] = _gammahalf_module()   # deep transcendental Gamma(1/2), via √π + 3<π<4
    out["ZetaNumerics"] = _zeta_module()     # zeta(2) bounds + zeta(3) > 9/8 (Apery, no closed form)
    out["ZetaEmitter"] = _zeta_emitter_module()  # reusable ZetaBoundCertificate: zeta(5),(6),(7) bounds
    out["QuarticJensen"] = _quartic_module()     # d=4 Jensen hyperbolicity (Delta4>0 & P<0 & D<0), n=0,1
    out["HankelJensen"] = _hankel_module()       # d=5 Jensen hyperbolicity (Hermite/Hankel minors), n=0
    out["Robin"] = _robin_module()               # Robin's criterion (RH-EQUIVALENT): comfortable n + all 13 SA numbers in (5040, 2e6]
    out["RobinReduction"] = _robin_reduction_module()  # D3: G-monotonicity reduction lemma (least counterexample is SA)
    out["NicolasBridge"] = _nicolas_module()           # D4: Nicolas=>Robin bridge phi*sigma<n^2 (primorial instances)
    return out


def root(mods) -> str:
    return ("/- RH library root -- every module is generated/frozen. -/\n"
            + "\n".join(f"import RH.{m}" for m in mods) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    mods = modules()
    files = {f"RH/{m}.lean": text for m, text in mods.items()}
    files["RH.lean"] = root(mods)
    if args.check:
        ok = True
        for rel, text in files.items():
            p = HERE / rel
            if not p.exists() or p.read_text() != text:
                ok = False
                print(f"DRIFT: {rel}")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    (HERE / "RH").mkdir(exist_ok=True)
    for rel, text in files.items():
        (HERE / rel).write_text(text)
    print(f"assembled RH library: {len(mods)} modules ({', '.join(mods)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
