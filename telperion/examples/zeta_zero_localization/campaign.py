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


def band_tag(den: int, lo: int, hi: int) -> str:
    return f"1d{den}_{den - 1}d{den}_{lo}_{hi}"


def band_module(den: int, lo: int, hi: int) -> str:
    return f"RHInBox_{band_tag(den, lo, hi)}"


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
    tag = band_tag(den, lo, hi)
    box = f"1/{den},{den - 1}/{den},{lo},{hi}"
    for density, prec in RETRY_LADDER:
        t0 = time.time()
        proc = subprocess.run(
            [sys.executable, str(GENERATE), "--box", box,
             "--prec", str(prec), "--density", str(density)],
            capture_output=True, text=True, cwd=str(HERE),
        )
        secs = round(time.time() - t0, 1)
        if proc.returncode == 0:
            n = None
            for line in proc.stdout.splitlines():
                if "winding N=" in line:
                    n = int(line.split("winding N=")[1].split(",")[0])
            return {"status": "ok", "n": n, "density": density,
                    "prec": prec, "secs": secs}
        last_err = (proc.stderr or proc.stdout).strip().splitlines()
        last_err = last_err[-1] if last_err else "unknown"
    return {"status": "refused", "error": last_err}


def cmd_emit_bands(args) -> int:
    bands = plan_bands(args.t_from, args.t_to)
    st = load_state()
    todo = []
    for den, lo, hi in bands:
        tag = band_tag(den, lo, hi)
        rec = st["bands"].get(tag)
        lean_file = LEAN_DIR / f"{band_module(den, lo, hi)}.lean"
        if rec and rec.get("status") == "ok" and lean_file.exists():
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


def _hyp(name: str, den: int, lo: int, hi: int) -> str:
    return (f"    ({name} : ∀ ρ : ℂ, (((1 / {den}) : ℝ) ≤ ρ.re ∧ "
            f"ρ.re ≤ (({den - 1} / {den}))) →\n"
            f"      ((({lo}) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ({hi})) → "
            f"riemannZeta ρ = 0 → ρ.re = 1 / 2)\n")


def _log_exp_bound(b: int) -> int:
    """Smallest L with 2.7^L >= b (so `Real.log b <= L` via 2.7 < e)."""
    L = 1
    while 2.7 ** L < b:
        L += 1
    return L


def emit_segment_file(prev_top: int, top: int, prev_bands: list, seg_bands: list) -> str:
    """AllZeros_h<top>.lean following the AllZeros_h4000 template."""
    K = len(seg_bands)
    den = seg_bands[0][0]
    L = _log_exp_bound(top)
    edges = [b[1] for b in seg_bands] + [seg_bands[-1][2]]
    A, B = prev_top, top

    out = []
    w = out.append
    w(f"/-  Height-chain step: all nontrivial zeta zeros up to height {B} on Re = 1/2 --\n"
      f"    `AllZeros_h{A}` + a `[{A}, {B}]` SEGMENT certificate ({K} bands, width 1/{den})\n"
      f"    composed by `AllZerosUpToHeight.height_chain`.  Emitted by campaign.py.\n"
      f"    conjecture1_proved = False. -/\n")
    w("import Mathlib\nimport DlvpZetaZeroFree\nimport DlvpZetaRateEffective\n"
      "import ZetaZeroConfinement\nimport AllZerosUpToHeight\n")
    w(f"import AllZeros_h{A}\n")
    for b in seg_bands:
        w(f"import {band_module(*b)}\n")
    w("\nopen Complex MeasureTheory Real\nopen scoped Topology\n\n")
    w(f"namespace AllZeros_h{B}\n\n")

    # bndSeg
    w(f"/-- The {K}-band partition of `[{A}, {B}]`. -/\n")
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

    # segment theorem
    w(f"/-- The `[{A}, {B}]` SEGMENT: every zero with `{A} ≤ Im ≤ {B}` is on the line. -/\n")
    w(f"theorem segment_{A}_{B}\n")
    for i, b in enumerate(seg_bands):
        w(_hyp(f"hseg{i}", *b))
    w(f"    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {B} → 55 / 16 ≤ |ρ.im|) :\n")
    w(f"    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ({A}:ℝ) ≤ ρ.im → ρ.im ≤ {B} → ρ.re = 1 / 2 := by\n")
    w(f"  have hre_eq : (1 : ℝ) - 1 / {den} = {den - 1} / {den} := by norm_num\n")
    w("  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line\n")
    w(f"    (1 / {den}) {A} {B} bndSeg {K} (by norm_num) bndSeg_mono rfl rfl haC_{B}\n")
    w("    (by norm_num) (by norm_num) ?_ hγ\n")
    w("  intro i hi ρ hre him hz\n")
    w(f"  have hre' : ((1 / {den}) : ℝ) ≤ ρ.re ∧ ρ.re ≤ {den - 1} / {den} := by\n")
    w("    refine ⟨hre.1, ?_⟩\n    have h2 := hre.2\n    linarith [h2, hre_eq]\n")
    w("  interval_cases i\n")
    for i in range(K):
        w(f"  · exact hseg{i} ρ hre' him hz\n")
    w("\n")

    # capstone _of_bands
    w(f"/-- **T = {B} via the HEIGHT CHAIN**: `[0,{A}]` (AllZeros_h{A}) ∘ `[{A},{B}]` (segment).\n"
      f"    conjecture1_proved = False. -/\n")
    w(f"theorem all_nontrivial_zeros_up_to_height_{B}_of_bands\n")
    for i, b in enumerate(prev_bands):
        w(_hyp(f"hband{i}", *b))
    for i, b in enumerate(seg_bands):
        w(_hyp(f"hseg{i}", *b))
    w(f"    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {B} → 55 / 16 ≤ |ρ.im|) :\n")
    w(f"    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {B} → ρ.re = 1 / 2 := by\n")
    w(f"  have hγ{A} : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {A} → 55 / 16 ≤ |ρ.im| :=\n")
    w(f"    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))\n")
    w(f"  exact AllZerosUpToHeight.height_chain {A} {B}\n")
    w(f"    (AllZeros_h{A}.all_nontrivial_zeros_up_to_height_{A}_of_bands\n")
    for i in range(len(prev_bands)):
        w(f"    hband{i}\n")
    w(f"      hγ{A})\n")
    w(f"    (segment_{A}_{B}\n")
    for i in range(len(seg_bands)):
        w(f"      hseg{i}\n")
    w("      hγ)\n\n")
    w(f"end AllZeros_h{B}\n")
    return "".join(out)


def cmd_emit_segment(args) -> int:
    top = args.upto
    # previous capstone: largest existing AllZeros_h<A> with A < top
    prevs = sorted(
        int(p.stem.split("_h")[1]) for p in LEAN_DIR.glob("AllZeros_h*.lean")
        if p.stem.split("_h")[1].isdigit() and int(p.stem.split("_h")[1]) < top
    )
    if not prevs:
        print("no previous AllZeros_h* capstone found", file=sys.stderr)
        return 1
    prev_top = prevs[-1]
    # prev hypothesis list: legacy ladder + campaign bands up to prev_top
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
            prints.append(f"#print axioms {mod}.rh_in_box_{band_tag(*b)}\n")
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
    for top in segment_tops(args.t_from, args.t_to):
        rc = cmd_emit_segment(argparse.Namespace(upto=top))
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
        if name == "register-lakefile":
            p.add_argument("--segments", action="store_true",
                           help="also register AllZeros_h<seg> modules")
    p = sub.add_parser("emit-segment")
    p.add_argument("--upto", type=int, required=True)
    sub.add_parser("status")
    args = ap.parse_args()
    return {"plan": cmd_plan, "emit-bands": cmd_emit_bands,
            "register-lakefile": cmd_register_lakefile,
            "emit-segment": cmd_emit_segment, "status": cmd_status,
            "guard-update": cmd_guard_update, "assemble": cmd_assemble}[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
