"""Height-ladder campaign orchestrator: tiled band certificates toward T = 10^6.

Drives the per-band `generate.py --box` emitter across a planned schedule of
bands, with checkpointing, parallel lanes, and the close-pair re-sweep retry
ladder; registers emitted modules in the lakefile; and emits the AllZeros_h<B>
segment/chain glue files following the AllZeros_h4000 template exactly.

    python3 campaign.py plan --from 4000 --to 8000            # show band schedule
    python3 campaign.py emit-bands --from 4000 --to 8000 --jobs 8
    python3 campaign.py register-lakefile --from 4000 --to 8000
    python3 campaign.py emit-segment --upto 6000              # AllZeros_h6000.lean
    python3 campaign.py status

Width policy (MILLION_ROADMAP): all bands from 4000 up are emitted at
a = 1/4,000,000 (valid to T = 10^6: a <= dlvpRateC / log T there).  The legacy
ladder ([0,4000] at 1/2,000,000) is consumed as-is through its width-free
conclusions -- the height chain composes segments of different widths.

Band-height policy: height h(T) = min(40, floor(2*pi*43 / log(T/2pi))) keeps
the per-band zero count n ~= 43 under the measured elaboration ceiling (~46).

Trust boundary: unchanged from the T=4000 milestone -- Arb enclosures ride as
the documented hLine/hArb hypotheses; the kernel verifies all implications.
conjecture1_proved = False.
"""
from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

HERE = Path(__file__).resolve().parent
LEAN_DIR = HERE / "lean"
GENERATE = HERE / "generate.py"
STATE = HERE / "campaign_state.json"
LAKEFILE = LEAN_DIR / "lakefile.toml"

WIDTH_DEN = 4_000_000          # campaign width a = 1/WIDTH_DEN (valid to 10^6)
LEGACY_DEN = 2_000_000         # the [0,4000] ladder width
TARGET_N = 43                  # zeros per band target (ceiling ~46 measured)
MAX_BAND_H = 40
SEG_BANDS = 50                 # bands per segment file (measured budget)
TURING_FROM = 1                # bands at/above this height use the T5 route
                               # (RHInBoxT_* modules; 10x cheaper Lean, 4x driver).
                               # Set to 1 for the FULL T5 RE-BASE (2026-09-12: the
                               # winding-route hArb was found over-quantified/vacuous
                               # -- see MILLION_CAMPAIGN doc HONESTY FLAG; the whole
                               # ladder [1, 24000] re-emits on T5, base = upTo_1).

# Retry ladder for close-pair refusals: (density, prec)
RETRY_LADDER = [(1.0, 300), (2.0, 300), (4.0, 300), (6.0, 300), (8.0, 450)]


# ---------------------------------------------------------------- band plans

def legacy_bands() -> list[tuple[int, int, int]]:
    """The frozen [0,4000] ladder at width 1/2e6: (den, lo, hi) in capstone order.

    39 bands to 2000 (h2000 chain) + 50 bands [2000,4000] (h4000 segment)."""
    bands = [(LEGACY_DEN, 0, 100)]
    lo = 100
    while lo < 1000:
        bands.append((LEGACY_DEN, lo, lo + 50))
        lo += 50
    while lo < 2000:
        bands.append((LEGACY_DEN, lo, lo + 50))
        lo += 50
    lo = 2000
    while lo < 4000:
        bands.append((LEGACY_DEN, lo, lo + 40))
        lo += 40
    return bands


def band_height(t: float) -> int:
    """Integer band height at T keeping n ~= TARGET_N zeros (density log(T/2pi)/2pi)."""
    dens = math.log(t / (2 * math.pi)) / (2 * math.pi)
    return max(1, min(MAX_BAND_H, int(TARGET_N / dens)))


BLOCK = 1000  # segment block height: tops land on round multiples of 1000


def plan_bands(t_from: int, t_to: int) -> list[tuple[int, int, int]]:
    """Campaign bands (den, lo, hi) covering [t_from, t_to] at width 1/WIDTH_DEN.

    Bands are planned per 1000-height block with integer edges landing exactly on
    the block tops, so every segment certificate ends at a round height and stays
    well under the SEG_BANDS budget."""
    bands = []
    a = t_from
    while a < t_to:
        b = min((a // BLOCK + 1) * BLOCK, t_to)
        n_bands = max(1, math.ceil((b - a) / band_height(max(a, 10))))
        for i in range(n_bands):
            lo = a + round(i * (b - a) / n_bands)
            hi = a + round((i + 1) * (b - a) / n_bands)
            if lo < hi:
                bands.append((WIDTH_DEN, lo, hi))
        a = b
    return bands


from fractions import Fraction

_POKE = Fraction(8, 100)  # conservative ball-poke clearance (actual = sqrt(2.25+h^2/4+1/16)-h/2
                          # ~= 2.31/h: 0.075 at h=31, smaller for taller bands; 0.08 covers h >= 29)


_STRETCH_CACHE_FILE = Path(__file__).resolve().parent / "edge_stretch.json"
_stretch_cache: dict | None = None


def _stretch_lookup(key: str):
    global _stretch_cache
    if _stretch_cache is None:
        _stretch_cache = (json.loads(_STRETCH_CACHE_FILE.read_text())
                          if _STRETCH_CACHE_FILE.exists() else {})
    return _stretch_cache.get(key)


def _stretch_store(key: str, val: str) -> None:
    _stretch_cache[key] = val
    tmp = _STRETCH_CACHE_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(_stretch_cache, sort_keys=True))
    tmp.replace(_STRETCH_CACHE_FILE)


def stretch_box(lo, hi):
    """Deterministic outward quarter-stretch of a band's certificate box.

    The nominal partition edge stays put; the band's BOX (what the T5
    certificate covers) stretches down/up by quarters until no zero ordinate
    lies within the ball-poke sliver outside the box.  Adjacent boxes may
    overlap — harmless (each certificate is independent; segment glue weakens
    bounds to the nominal partition).  Returns (box_lo, box_hi) Fractions.
    Results are cached per edge (Platt queries are ~0.3 s each)."""
    from telperion.arb_platt import PLATT_AVAILABLE, zeros_in_interval
    lo, hi = Fraction(lo), Fraction(hi)
    if not PLATT_AVAILABLE:
        return lo, hi

    def _clear(edge, direction):
        key = f"{direction}:{edge}"
        hit = _stretch_lookup(key)
        if hit is not None:
            return Fraction(hit)
        for k in range(5):
            cand = edge - Fraction(k, 4) if direction == "down" else edge + Fraction(k, 4)
            if direction == "down":
                zs = zeros_in_interval(cand - 1, cand)
                ok = all(hz < cand - _POKE for _lz, hz in zs)
            else:
                zs = zeros_in_interval(cand, cand + 1)
                ok = all(lz > cand + _POKE for lz, _hz in zs)
            if ok:
                _stretch_store(key, str(cand))
                return cand
        raise RuntimeError(f"stretch_box: no clear {direction} edge near {edge}")

    return _clear(lo, "down"), _clear(hi, "up")


def band_box(den: int, lo, hi):
    """The certificate box for a band: stretched on the T5 route, nominal otherwise."""
    if int(lo) >= TURING_FROM:
        blo, bhi = stretch_box(lo, hi)
        return den, blo, bhi
    return den, Fraction(lo), Fraction(hi)


def band_tag(den: int, lo, hi) -> str:
    def _f(v):
        v = Fraction(v)
        return f"{v.numerator}" if v.denominator == 1 else f"{v.numerator}d{v.denominator}"
    return f"1d{den}_{den - 1}d{den}_{_f(lo)}_{_f(hi)}"


def band_module(den: int, lo, hi) -> str:
    prefix = "RHInBoxT_" if int(lo) >= TURING_FROM else "RHInBox_"
    return f"{prefix}{band_tag(*band_box(den, lo, hi))}"


# ---------------------------------------------------------------- state

def load_state() -> dict:
    if STATE.exists():
        return json.loads(STATE.read_text())
    return {"bands": {}}


def save_state(st: dict) -> None:
    tmp = STATE.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(st, indent=1, sort_keys=True))
    tmp.replace(STATE)


# ---------------------------------------------------------------- emit-bands

def emit_one_band(den: int, lo: int, hi: int) -> dict:
    """Run the per-band driver with the retry ladder.  Returns a state record."""
    bden, blo, bhi = band_box(den, lo, hi)
    tag = band_tag(bden, blo, bhi)
    box = f"1/{den},{den - 1}/{den},{blo},{bhi}"
    turing = int(lo) >= TURING_FROM
    for density, prec in RETRY_LADDER:
        t0 = time.time()
        cmd = [sys.executable, str(GENERATE), "--box", box,
               "--prec", str(prec), "--density", str(density)]
        if turing:
            cmd.append("--turing")
        proc = subprocess.run(cmd, capture_output=True, text=True, cwd=str(HERE))
        secs = round(time.time() - t0, 1)
        if proc.returncode == 0:
            n = None
            for line in proc.stdout.splitlines():
                for key in ("winding N=", "edge count N="):
                    if key in line:
                        n = int(line.split(key)[1].split(",")[0])
            return {"status": "ok", "n": n, "density": density,
                    "prec": prec, "secs": secs, "route": "t5" if turing else "wind"}
        last_err = (proc.stderr or proc.stdout).strip().splitlines()
        last_err = last_err[-1] if last_err else "unknown"
    return {"status": "refused", "error": last_err}


def cmd_emit_bands(args) -> int:
    bands = plan_bands(args.t_from, args.t_to)
    st = load_state()
    todo = []
    force = getattr(args, "force", False)
    for den, lo, hi in bands:
        tag = band_tag(den, lo, hi)
        rec = st["bands"].get(tag)
        lean_file = LEAN_DIR / f"{band_module(den, lo, hi)}.lean"
        sidecar = lean_file.with_suffix(".cert.json")
        needs_gate = int(lo) >= TURING_FROM and not sidecar.exists()
        if (rec and rec.get("status") == "ok" and lean_file.exists()
                and not force and not needs_gate):
            continue
        todo.append((den, lo, hi))
    print(f"{len(bands)} bands planned, {len(bands) - len(todo)} done, "
          f"{len(todo)} to emit; jobs={args.jobs}")
    n_ok = n_fail = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(emit_one_band, den, lo, hi): (den, lo, hi)
                for den, lo, hi in todo}
        for fut in as_completed(futs):
            den, lo, hi = futs[fut]
            tag = band_tag(den, lo, hi)
            rec = fut.result()
            st["bands"][tag] = rec
            save_state(st)
            if rec["status"] == "ok":
                n_ok += 1
                print(f"  [{n_ok + n_fail}/{len(todo)}] {tag}: N={rec['n']} "
                      f"(density={rec['density']}, {rec['secs']}s)")
            else:
                n_fail += 1
                print(f"  [{n_ok + n_fail}/{len(todo)}] {tag}: REFUSED -- "
                      f"{rec['error'][:200]}")
    print(f"emit-bands done: {n_ok} ok, {n_fail} refused")
    return 0 if n_fail == 0 else 1


# ---------------------------------------------------------------- lakefile

def cmd_register_lakefile(args) -> int:
    bands = plan_bands(args.t_from, args.t_to)
    text = LAKEFILE.read_text()
    added = []
    new_libs = []
    mods = [band_module(*b) for b in bands]
    if args.segments:
        mods += [f"AllZeros_h{b}" for b in segment_tops(args.t_from, args.t_to)]
    for mod in mods:
        if f'"{mod}"' in text:
            continue
        new_libs.append(f'[[lean_lib]]\nname = "{mod}"\n')
        # extend defaultTargets (first line contains the array)
        text = text.replace(']\n', f', "{mod}"]\n', 1) if text.startswith(
            "defaultTargets") else text
        added.append(mod)
    if not added:
        print("lakefile: nothing to add")
        return 0
    # defaultTargets: insert before the closing bracket of the first line
    lines = text.splitlines(keepends=True)
    for i, ln in enumerate(lines):
        if ln.startswith("defaultTargets"):
            close = ln.rstrip()
            assert close.endswith("]")
            names = ", ".join(f'"{m}"' for m in added)
            lines[i] = close[:-1] + f", {names}]\n"
            break
    text = "".join(lines) + "".join(new_libs)
    LAKEFILE.write_text(text)
    print(f"lakefile: added {len(added)} modules")
    return 0


# ---------------------------------------------------------------- segments

def segment_tops(t_from: int, t_to: int) -> list[int]:
    """Segment top heights: the round 1000-block tops."""
    tops = []
    a = t_from
    while a < t_to:
        b = min((a // BLOCK + 1) * BLOCK, t_to)
        tops.append(b)
        a = b
    return tops


def _fr(v) -> str:
    v = Fraction(v)
    return f"{v.numerator}" if v.denominator == 1 else f"{v.numerator} / {v.denominator}"


def _hyp(name: str, den: int, lo, hi) -> str:
    return (f"    ({name} : ∀ ρ : ℂ, (((1 / {den}) : ℝ) ≤ ρ.re ∧ "
            f"ρ.re ≤ (({den - 1} / {den}))) →\n"
            f"      ((({_fr(lo)}) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ({_fr(hi)})) → "
            f"riemannZeta ρ = 0 → ρ.re = 1 / 2)\n")


def _log_exp_bound(b: int) -> int:
    """Smallest L with 2.7^L >= b (so `Real.log b <= L` via 2.7 < e)."""
    L = 1
    while 2.7 ** L < b:
        L += 1
    return L


def emit_segment_file(prev_top: int, top: int, prev_bands: list, seg_bands: list) -> str:
    """AllZeros_h<top>.lean — INDEXED segment/capstone form (B1).

    `prev_bands` is unused by the indexed form (the previous capstone now
    consumes one hypothesis per PRIOR SEGMENT via its own `BandHyp` predicate,
    not per band).  It is kept in the signature for call-site compatibility.

    Shape:
      * `bndSeg`/`bndSeg_mono` — the nominal `[A, B]` partition (unchanged);
      * `bLo`/`bHi` — the per-band STRETCHED certificate-box edges (`band_box`);
      * `hcover : ∀ i, i < K → bLo i ≤ bndSeg i ∧ bndSeg (i+1) ≤ bHi i` — one
        `interval_cases`+`norm_num` proof weakening nominal→stretched;
      * `BandHyp` — the segment's ONE indexed band hypothesis (re-range at the
        campaign width + STRETCHED im-range `bLo i .. bHi i`);
      * `segment_A_B` — takes one `hbands : BandHyp` (+ hγ), forwards to the
        kernel lemma weakening the nominal partition bounds via `hcover`;
      * capstone `all_...of_bands` — takes ONE `hbands_<segTop>` per prior
        segment (typed `AllZeros_h<segTop>.BandHyp`) plus its own `hbands`,
        forwarding positionally to the previous capstone + `segment_A_B`.
    """
    K = len(seg_bands)
    den = seg_bands[0][0]
    L = _log_exp_bound(top)
    edges = [b[1] for b in seg_bands] + [seg_bands[-1][2]]
    boxes = [band_box(*b) for b in seg_bands]          # (den, blo, bhi) stretched
    A, B = prev_top, top
    re_lo = f"(1 / {den})"
    re_hi = f"{den - 1} / {den}"
    # prior segment tops (one BandHyp binder per prior segment): [1000, 2000, ..., A]
    prior_tops = [] if A == 1 else segment_tops(1, A)

    out = []
    w = out.append
    w(f"/-  Height-chain step: all nontrivial zeta zeros up to height {B} on Re = 1/2 --\n"
      f"    `AllZeros_h{A}` + a `[{A}, {B}]` SEGMENT certificate ({K} bands, width 1/{den})\n"
      f"    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form\n"
      f"    (B1): one `BandHyp` per segment instead of per-band binders.\n"
      f"    Emitted by campaign.py.  conjecture1_proved = False. -/\n")
    w("import Mathlib\nimport DlvpZetaZeroFree\nimport DlvpZetaRateEffective\n"
      "import ZetaZeroConfinement\nimport AllZerosUpToHeight\n")
    if A != 1:
        w(f"import AllZeros_h{A}\n")
    for b in seg_bands:
        w(f"import {band_module(*b)}\n")
    w("\nopen Complex MeasureTheory Real\nopen scoped Topology\n\n")
    w(f"namespace AllZeros_h{B}\n\n")

    # bndSeg (nominal partition)
    w(f"/-- The {K}-band NOMINAL partition of `[{A}, {B}]`. -/\n")
    w("noncomputable def bndSeg : ℕ → ℝ := fun i => match i with\n")
    for i, e in enumerate(edges):
        w(f"  | {i} => {e}\n")
    w(f"  | _ => {B}\n\n")

    # bndSeg_mono
    w("theorem bndSeg_mono : Monotone bndSeg := by\n")
    w("  refine monotone_nat_of_le_succ ?_\n  intro nn\n")
    pat = " | ".join(["_"] * (K + 1))
    w(f"  rcases nn with {pat} | nn\n")
    for i in range(K + 1):
        a, b2 = edges[min(i, K)], edges[min(i + 1, K)]
        w(f"  · show (({a}:ℝ)) ≤ ({b2}); norm_num\n")
    w("  · exact le_refl _\n\n")

    # bLo / bHi (stretched certificate-box edges, per band)
    w(f"/-- The lower edges of the {K} STRETCHED certificate boxes. -/\n")
    w("noncomputable def bLo : ℕ → ℝ := fun i => match i with\n")
    for i, (_d, blo, _bhi) in enumerate(boxes):
        w(f"  | {i} => {_fr(blo)}\n")
    w(f"  | _ => {_fr(boxes[-1][1])}\n\n")
    w(f"/-- The upper edges of the {K} STRETCHED certificate boxes. -/\n")
    w("noncomputable def bHi : ℕ → ℝ := fun i => match i with\n")
    for i, (_d, _blo, bhi) in enumerate(boxes):
        w(f"  | {i} => {_fr(bhi)}\n")
    w(f"  | _ => {_fr(boxes[-1][2])}\n\n")

    # hcover : nominal partition ⊆ stretched box, band by band
    w(f"/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched\n"
      f"    certificate box `[bLo i, bHi i]`. -/\n")
    w(f"theorem hcover : ∀ i, i < {K} → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by\n")
    w("  intro i hi\n")
    w("  interval_cases i <;>\n")
    w("    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩\n\n")

    # haC
    w(f"/-- `1/{den} ≤ dlvpRateC / log {B}` (`log {B} ≤ {L}`, `2.7^{L} ≥ {B}`). -/\n")
    w(f"theorem haC_{B} : (1 / {den} : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log {B} := by\n")
    w(f"  have hlog : Real.log {B} ≤ {L} := by\n")
    w("    rw [Real.log_le_iff_le_exp (by norm_num)]\n")
    w("    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]\n")
    w(f"    have h{L} : Real.exp {L} = (Real.exp 1) ^ {L} := by rw [← Real.exp_nat_mul]; norm_num\n")
    w(f"    have hpow : (2.7 : ℝ) ^ {L} ≤ (Real.exp 1) ^ {L} := pow_le_pow_left₀ (by norm_num) he1 {L}\n")
    w(f"    rw [h{L}]; nlinarith [hpow]\n")
    w(f"  have hpos : 0 < Real.log {B} := Real.log_pos (by norm_num)\n")
    w("  rw [le_div_iff₀ hpos]\n")
    w(f"  calc (1 / {den} : ℝ) * Real.log {B}\n")
    w(f"      ≤ (1 / {den}) * {L} := by nlinarith [hlog, hpos]\n")
    w("    _ ≤ 9 / 1369088 := by norm_num\n")
    w("    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower\n\n")

    # BandHyp — the ONE indexed band hypothesis for this segment (stretched boxes).
    w(f"/-- The `[{A}, {B}]` segment's band hypothesis: every band `i < {K}` certifies\n"
      f"    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the {K} per-band\n"
      f"    hypotheses; the previous capstone consumes one such predicate per segment. -/\n")
    w("def BandHyp : Prop :=\n")
    w(f"  ∀ i, i < {K} → ∀ ρ : ℂ, (({re_lo} : ℝ) ≤ ρ.re ∧ ρ.re ≤ ({re_hi})) →\n")
    w("    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2\n\n")

    # segment theorem — takes ONE hbands : BandHyp; weakens nominal→stretched via hcover.
    w(f"/-- The `[{A}, {B}]` SEGMENT: every zero with `{A} ≤ Im ≤ {B}` is on the line. -/\n")
    w(f"theorem segment_{A}_{B} (hbands : BandHyp)\n")
    w(f"    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {B} → 55 / 16 ≤ |ρ.im|) :\n")
    w(f"    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ({A}:ℝ) ≤ ρ.im → ρ.im ≤ {B} → ρ.re = 1 / 2 := by\n")
    w(f"  have hre_eq : (1 : ℝ) - 1 / {den} = {den - 1} / {den} := by norm_num\n")
    w("  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line\n")
    w(f"    (1 / {den}) {A} {B} bndSeg {K} (by norm_num) bndSeg_mono rfl rfl haC_{B}\n")
    w("    (by norm_num) (by norm_num) ?_ hγ\n")
    w("  intro i hi ρ hre him hz\n")
    w(f"  have hre' : (({re_lo}) : ℝ) ≤ ρ.re ∧ ρ.re ≤ {re_hi} := by\n")
    w("    refine ⟨hre.1, ?_⟩\n    have h2 := hre.2\n    linarith [h2, hre_eq]\n")
    w("  obtain ⟨hcov1, hcov2⟩ := hcover i hi\n")
    w("  exact hbands i hi ρ hre'\n")
    w("    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz\n\n")

    # base lemma (re-based ladder bottom): upTo-1 is vacuous below the 55/16 floor
    if A == 1:
        w("/-- Below height 1 the ladder is vacuous: the height floor `55/16 ≤ |Im ρ|`\n"
          "    (carried `hγ`, discharged by StripClear at assembly) contradicts `Im ρ ≤ 1`. -/\n")
        w("theorem upTo_1\n")
        w("    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1 → 55 / 16 ≤ |ρ.im|) :\n")
        w("    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1 → ρ.re = 1 / 2 := by\n")
        w("  intro ρ hz h0 h1\n")
        w("  have h := hγ ρ hz h0 h1\n")
        w("  rw [abs_of_pos h0] at h\n")
        w("  have habs : (55 / 16 : ℝ) ≤ 1 := le_trans h h1\n")
        w("  norm_num at habs\n\n")

    # capstone _of_bands — one hbands_<segTop> per prior segment + own hbands.
    w(f"/-- **T = {B} via the HEIGHT CHAIN**: `[0,{A}]` ∘ `[{A},{B}]` (segment).\n"
      f"    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/\n")
    w(f"theorem all_nontrivial_zeros_up_to_height_{B}_of_bands\n")
    for pt in prior_tops:
        w(f"    (hbands_{pt} : AllZeros_h{pt}.BandHyp)\n")
    w("    (hbands : BandHyp)\n")
    w(f"    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {B} → 55 / 16 ≤ |ρ.im|) :\n")
    w(f"    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {B} → ρ.re = 1 / 2 := by\n")
    w(f"  have hγ{A} : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {A} → 55 / 16 ≤ |ρ.im| :=\n")
    w(f"    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))\n")
    w(f"  exact AllZerosUpToHeight.height_chain {A} {B}\n")
    if A == 1:
        w(f"    (upTo_1 hγ{A})\n")
    else:
        w(f"    (AllZeros_h{A}.all_nontrivial_zeros_up_to_height_{A}_of_bands\n")
        for pt in prior_tops:
            w(f"      hbands_{pt}\n")
        w(f"      hγ{A})\n")
    w(f"    (segment_{A}_{B} hbands hγ)\n\n")
    w(f"end AllZeros_h{B}\n")
    return "".join(out)


def cmd_emit_segment(args) -> int:
    top = args.upto
    if getattr(args, "base", None) == 1:
        # re-based ladder bottom: upTo_1 (vacuous below the 55/16 floor) + [1, top]
        prev_top = 1
        prev_bands = []
    else:
        # previous capstone: largest existing AllZeros_h<A> with A < top
        # (in the re-based world, only re-generated capstones >= 1000 count)
        floor_prev = 1000 if TURING_FROM <= 1 else 0
        prevs = sorted(
            int(p.stem.split("_h")[1]) for p in LEAN_DIR.glob("AllZeros_h*.lean")
            if p.stem.split("_h")[1].isdigit()
            and floor_prev <= int(p.stem.split("_h")[1]) < top
        )
        if not prevs:
            print("no previous AllZeros_h* capstone found", file=sys.stderr)
            return 1
        prev_top = prevs[-1]
        if TURING_FROM <= 1:
            prev_bands = plan_bands(1, prev_top)
        else:
            prev_bands = list(legacy_bands())
            if prev_top < 4000:
                print(f"previous capstone {prev_top} < 4000 unsupported", file=sys.stderr)
                return 1
            if prev_top > 4000:
                prev_bands += plan_bands(4000, prev_top)
    seg_bands = plan_bands(prev_top, top)
    if len(seg_bands) > SEG_BANDS:
        print(f"segment [{prev_top},{top}] has {len(seg_bands)} bands > {SEG_BANDS} budget",
              file=sys.stderr)
        return 1
    # all band lean files must exist
    missing = [band_module(*b) for b in seg_bands
               if not (LEAN_DIR / f"{band_module(*b)}.lean").exists()]
    if missing:
        print(f"missing band modules: {missing[:5]}...", file=sys.stderr)
        return 1
    text = emit_segment_file(prev_top, top, prev_bands, seg_bands)
    out = LEAN_DIR / f"AllZeros_h{top}.lean"
    out.write_text(text)
    print(f"wrote {out} ({len(text)} bytes): chain h{prev_top} + [{prev_top},{top}] "
          f"({len(seg_bands)} bands, {len(prev_bands)} carried hypotheses)")
    return 0


GUARD = LEAN_DIR / "AxiomGuardRHInBox.lean"


def cmd_guard_update(args) -> int:
    """Add imports + #print axioms entries for new bands and capstones."""
    bands = plan_bands(args.t_from, args.t_to)
    tops = segment_tops(args.t_from, args.t_to)
    text = GUARD.read_text()
    imports, prints = [], []
    for b in bands:
        mod = band_module(*b)
        if f"import {mod}\n" not in text:
            imports.append(f"import {mod}\n")
            prints.append(f"#print axioms {mod}.rh_in_box_{band_tag(*band_box(*b))}\n")
    prev = None
    for i, top in enumerate(tops):
        mod = f"AllZeros_h{top}"
        a = tops[i - 1] if i else args.t_from
        if f"import {mod}\n" not in text and (LEAN_DIR / f"{mod}.lean").exists():
            imports.append(f"import {mod}\n")
            prints.append(f"#print axioms {mod}.haC_{top}\n")
            prints.append(f"#print axioms {mod}.segment_{a}_{top}\n")
            prints.append(f"#print axioms {mod}.all_nontrivial_zeros_up_to_height_{top}_of_bands\n")
    if not imports:
        print("guard: nothing to add")
        return 0
    lines = text.splitlines(keepends=True)
    last_import = max(i for i, ln in enumerate(lines) if ln.startswith("import "))
    lines[last_import + 1:last_import + 1] = imports
    text = "".join(lines) + "".join(prints)
    GUARD.write_text(text)
    print(f"guard: added {len(imports)} imports, {len(prints)} print-axioms entries")
    return 0


def cmd_assemble(args) -> int:
    """One-shot leg assembly: register-lakefile + emit all segments + guard-update."""
    rc = cmd_register_lakefile(argparse.Namespace(
        t_from=args.t_from, t_to=args.t_to, segments=True))
    if rc:
        return rc
    tops = segment_tops(args.t_from, args.t_to)
    for top in tops:
        base = 1 if (args.t_from == 1 and top == tops[0]) else None
        rc = cmd_emit_segment(argparse.Namespace(upto=top, base=base))
        if rc:
            return rc
    return cmd_guard_update(args)


def cmd_plan(args) -> int:
    bands = plan_bands(args.t_from, args.t_to)
    dens_lo = math.log(args.t_from / (2 * math.pi)) / (2 * math.pi) if args.t_from > 7 else 0
    dens_hi = math.log(args.t_to / (2 * math.pi)) / (2 * math.pi)
    est = sum((b[2] - b[1]) * math.log((b[1] + b[2]) / (4 * math.pi)) / (2 * math.pi)
              for b in bands)
    print(f"[{args.t_from}, {args.t_to}]: {len(bands)} bands, ~{est:.0f} zeros, "
          f"density {dens_lo:.2f}->{dens_hi:.2f}/unit")
    print(f"segments end at: {segment_tops(args.t_from, args.t_to)}")
    for den, lo, hi in bands[:3] + bands[-3:]:
        print(f"  [{lo},{hi}] h={hi - lo} width=1/{den}")
    return 0


def cmd_verify_bands(args) -> int:
    """Post-hoc statement_match audit: for sampled T5 bands, check the compiled
    band theorem's type is defeq to `TuringBand.BandStatement <params>` with the
    params re-rendered INDEPENDENTLY from the `.cert.json` sidecar (one batched
    `lake env lean` run).  Includes a doctored negative control (n+1) that must
    MISMATCH — a run whose negative control passes is itself a failure."""
    import random

    from telperion.statement_match import statement_match_check

    sidecars = sorted(LEAN_DIR.glob("RHInBoxT_*.cert.json"))
    if args.sample and len(sidecars) > args.sample:
        rng = random.Random(args.seed)
        sidecars = sorted(rng.sample(sidecars, args.sample))
    if not sidecars:
        print("verify-bands: no .cert.json sidecars found")
        return 1

    def _btype(cert, n):
        e = {k: (cert["edges"][k][0], cert["edges"][k][1]) for k in cert["edges"]}
        def fr(s):
            f = Fraction(s)
            return f"({f.numerator} / {f.denominator} : ℝ)" if f.denominator != 1 \
                else f"({f.numerator} : ℝ)"
        ns = None  # filled by caller
        return (f"TuringBand.BandStatement {fr(cert['re_lo'])} {fr(cert['re_hi'])} "
                f"{fr(cert['im_lo'])} {fr(cert['im_hi'])} {n} "
                + " ".join(fr(e[k][i]) for k in ("av2", "aht", "ahb", "ag1", "ag2")
                           for i in (0, 1))
                + " {NS}.cPB {NS}.RPB {NS}.hs1PB")

    intended, imports = {}, ["import Mathlib", "import TuringBand"]
    neg_name = None
    for i, sc in enumerate(sidecars):
        cert = json.loads(sc.read_text())
        ns = sc.name[: -len(".cert.json")]
        tag = ns[len("RHInBoxT_"):]
        imports.append(f"import {ns}")
        intended[f"{ns}.rh_in_box_{tag}"] = _btype(cert, cert["n"]).replace("{NS}", ns)
        if i == 0:  # negative control: doctored count must MISMATCH
            neg_name = f"{ns}.rh_in_box_{tag}"
            intended["__NEGCTRL__"] = _btype(cert, cert["n"] + 1).replace("{NS}", ns)
    # run the real checks
    neg_type = intended.pop("__NEGCTRL__")
    res = statement_match_check(intended, env_dir=str(LEAN_DIR),
                                imports=tuple(imports))
    print(res.summary())
    negres = statement_match_check({neg_name: neg_type}, env_dir=str(LEAN_DIR),
                                   imports=tuple(imports))
    if negres.all_match:
        print("NEGATIVE CONTROL FAILED TO FAIL — audit invalid")
        return 1
    print(f"negative control (n+1) correctly MISMATCHED for {neg_name}")
    return 0 if res.all_match else 1


def cmd_status(args) -> int:
    st = load_state()
    ok = [t for t, r in st["bands"].items() if r.get("status") == "ok"]
    bad = [t for t, r in st["bands"].items() if r.get("status") != "ok"]
    nz = sum(r.get("n") or 0 for r in st["bands"].values() if r.get("status") == "ok")
    print(f"bands ok: {len(ok)}  refused: {len(bad)}  zeros certified in bands: {nz}")
    for t in bad:
        print(f"  REFUSED {t}: {st['bands'][t].get('error', '')[:150]}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("plan", "emit-bands", "register-lakefile", "guard-update", "assemble"):
        p = sub.add_parser(name)
        p.add_argument("--from", dest="t_from", type=int, required=True)
        p.add_argument("--to", dest="t_to", type=int, required=True)
        if name == "emit-bands":
            p.add_argument("--jobs", type=int, default=8)
            p.add_argument("--force", action="store_true",
                           help="re-emit even if the band file exists")
        if name == "register-lakefile":
            p.add_argument("--segments", action="store_true",
                           help="also register AllZeros_h<seg> modules")
    p = sub.add_parser("emit-segment")
    p.add_argument("--upto", type=int, required=True)
    p.add_argument("--base", type=int, default=None,
                   help="1 = re-based ladder bottom (upTo_1 base lemma, no prev import)")
    sub.add_parser("status")
    p = sub.add_parser("verify-bands")
    p.add_argument("--sample", type=int, default=12,
                   help="number of sidecars to audit (0 = all)")
    p.add_argument("--seed", type=int, default=20260912)
    args = ap.parse_args()
    return {"plan": cmd_plan, "emit-bands": cmd_emit_bands,
            "register-lakefile": cmd_register_lakefile,
            "emit-segment": cmd_emit_segment, "status": cmd_status,
            "guard-update": cmd_guard_update, "assemble": cmd_assemble,
            "verify-bands": cmd_verify_bands}[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
