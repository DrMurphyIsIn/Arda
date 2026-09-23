#!/usr/bin/env python3
"""emit_band_glue.py -- emit the K0/K1 band-glue instantiation of one ladder segment.

Brick K0 of the ANDURIL Arb discharge (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md,
section 1.3).  Given a segment file `AllZeros_h<H>.lean` of the zeta_zero_localization ladder,
this reads the segment's box table (`bLo`, `bHi`, band count) and, for every band, the emitted
band module `RHInBoxT_*.lean` (its `statement_match` arguments and its Blaschke ball `cPB`,
`RPB = sqrt q`), then writes a Lean module that

  * tabulates the bands as `BandGlue.BandData` (parameters copied VERBATIM from each band's
    `statement_match`, ball constants referenced by name),
  * proves `seg_edge` (table edges = the segment's `bLo`/`bHi`), `seg_stmt` (each table entry's
    band statement holds: it IS the band module's `statement_match`, checked by the kernel up to
    definitional unfolding), and `seg_geom` (the K1 cap geometry, with slab heights `capLo i`,
    `capHi i` = the band's own ball caps rounded UP to a multiple of 1/RES),
  * composes them into `bandHyp_of_inputs`, `bandHyp_of_reduced` (the segment's `BandHyp`) and the
    height-H corollaries.

A transcription error in the table cannot produce a wrong theorem: `seg_stmt` only type-checks if
every table entry is definitionally the band module's own parameters.

The cap geometry is checked here in exact rational arithmetic before emitting (the Lean side
re-checks it by `norm_num`).  The slab heights are tight on purpose: the slab
`(0, 1) x [T0 - capLo, T0]` must reach past the ball cap AND stay zero-free, and on the h280000
ladder the gap between a cap and the nearest zero beyond the edge is as small as 4.3e-5 (a round
height such as 1/10 would make about 385 of the 10,379 slab hypotheses false).  RES = 10^6 leaves
< 1e-6 of overshoot.

Usage:  emit_band_glue.py <zzl_lean_dir> <H> <out.lean> [--res 1000000] [--probe]
        emit_band_glue.py <zzl_lean_dir> <H> <out.lean> --ladder [--prefix Probes.]   (capstone-level)
conjecture1_proved = False.
"""
import argparse
import re
import sys
from fractions import Fraction
from pathlib import Path


def top_level_tokens(s):
    """Split s into top-level tokens: balanced (...) groups or bare words."""
    toks, i, n = [], 0, len(s)
    while i < n:
        ch = s[i]
        if ch.isspace():
            i += 1
            continue
        if ch == '(':
            depth, j = 0, i
            while j < n:
                if s[j] == '(':
                    depth += 1
                elif s[j] == ')':
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            toks.append(s[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] != '(':
                j += 1
            toks.append(s[i:j])
            i = j
    return toks


def strip_parens(t):
    t = t.strip()
    while t.startswith('(') and t.endswith(')'):
        # only strip if the outer parens match each other
        depth = 0
        ok = True
        for k, ch in enumerate(t):
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0 and k != len(t) - 1:
                    ok = False
                    break
        if not ok:
            break
        t = t[1:-1].strip()
    return t


def rat(t):
    """Parse a Lean rational literal text: `a`, `-a`, `a / b`, `-a / b`, possibly parenthesized,
    possibly with a trailing `: ℝ` ascription."""
    t = strip_parens(t)
    t = re.sub(r':\s*ℝ\s*$', '', t).strip()
    t = strip_parens(t)
    m = re.fullmatch(r'(-?\s*\d+)\s*/\s*(\d+)', t)
    if m:
        return Fraction(int(m.group(1).replace(' ', '')), int(m.group(2)))
    m = re.fullmatch(r'-?\s*\d+', t)
    if m:
        return Fraction(int(t.replace(' ', '')))
    raise ValueError(f'cannot parse rational {t!r}')


def parse_band(path):
    txt = path.read_text()
    mod = path.stem
    m = re.search(r'theorem statement_match :\s*TuringBand\.BandStatement(.*?):=', txt, re.S)
    if not m:
        raise ValueError(f'{mod}: no statement_match')
    toks = top_level_tokens(m.group(1))
    if len(toks) != 18 or toks[15:] != ['cPB', 'RPB', 'hs1PB']:
        raise ValueError(f'{mod}: unexpected statement_match args {toks}')
    mc = re.search(r'noncomputable def cPB : ℂ := ⟨(.*)⟩\s*$', txt, re.M)
    mr = re.search(r'noncomputable def RPB : ℝ := Real\.sqrt (.*)$', txt, re.M)
    if not (mc and mr):
        raise ValueError(f'{mod}: no cPB/RPB')
    cre_t, cim_t = top_level_tokens(mc.group(1).replace(',', ' '))
    q_t = mr.group(1).strip()
    return {
        'mod': mod,
        'sig0': rat(toks[0]), 'sig1': rat(toks[1]),
        'T0_t': toks[2], 'T1_t': toks[3], 'n_t': toks[4], 'LH_t': toks[5:15],
        'T0': rat(toks[2]), 'T1': rat(toks[3]), 'n': int(toks[4]),
        'LH': [rat(x) for x in toks[5:15]],
        'cre': rat(cre_t), 'cim': rat(cim_t), 'q': rat(q_t),
        'cim_t': strip_parens(cim_t), 'q_t': strip_parens(q_t),
    }


def parse_table(txt, name):
    m = re.search(r'noncomputable def ' + name + r' : ℕ → ℝ := fun i => match i with\n(.*?)\n\n',
                  txt, re.S)
    if not m:
        raise ValueError(f'no table {name}')
    tab = {}
    for line in m.group(1).splitlines():
        mm = re.match(r'\s*\|\s*(\d+|_)\s*=>\s*(.*)$', line)
        if mm and mm.group(1) != '_':
            tab[int(mm.group(1))] = (mm.group(2).strip(), rat(mm.group(2)))
    return tab


def parse_segment(zdir, H):
    seg = zdir / f'AllZeros_h{H}.lean'
    txt = seg.read_text()
    mods = re.findall(r'^import (RHInBoxT_\S+)$', txt, re.M)
    m = re.search(r'def BandHyp : Prop :=\s*∀ i, i < (\d+) →', txt)
    if not m:
        raise ValueError('no BandHyp count')
    count = int(m.group(1))
    lo, hi = parse_table(txt, 'bLo'), parse_table(txt, 'bHi')
    bands = [parse_band(zdir / f'{mod}.lean') for mod in mods]
    if len(bands) != count:
        raise ValueError(f'{len(bands)} band imports vs count {count}')
    # Match each box i to the band whose (T0, T1) are (bLo i, bHi i).
    by_edges = {}
    for b in bands:
        by_edges.setdefault((b['T0'], b['T1']), []).append(b)
    order = []
    for i in range(count):
        cand = by_edges.get((lo[i][1], hi[i][1]), [])
        if len(cand) != 1:
            raise ValueError(f'box {i}: {len(cand)} bands with edges {lo[i][1]}, {hi[i][1]}')
        order.append(cand[0])
    return seg.stem, count, order


def cap_check(b, dlo, dhi):
    """Exact check of the CapGeom side conditions with slab heights dlo (bottom), dhi (top)."""
    cim, q, T0, T1 = b['cim'], b['q'], b['T0'], b['T1']
    lo0 = cim - T0 + dlo
    hi0 = T1 + dhi - cim
    conds = [T0 != 0, T1 != 0, dlo >= 0, dhi >= 0, cim >= 0, q <= cim * cim,
             lo0 >= 0, q <= lo0 * lo0, hi0 >= 0, q <= hi0 * hi0]
    return all(conds)


def cap_round_up(q, base, res):
    """Smallest m / res (m integer >= 0) with sqrt(q) <= base + m / res, exactly (base rational)."""
    import math
    m = max(0, math.floor((math.sqrt(q) - base) * res) - 2)
    while True:
        v = base + Fraction(m, res)
        if v >= 0 and q <= v * v:
            return Fraction(m, res)
        m += 1


def band_caps(b, res):
    """(capLo, capHi): the bottom and top ball caps of band b, rounded up to 1/res."""
    cim, q, T0, T1 = b['cim'], b['q'], b['T0'], b['T1']
    # bottom: T0 - dlo <= cim - sqrt q  <=>  sqrt q <= (cim - T0) + dlo
    # top:    cim + sqrt q <= T1 + dhi  <=>  sqrt q <= (T1 - cim) + dhi
    return cap_round_up(q, cim - T0, res), cap_round_up(q, T1 - cim, res)


def caps(b):
    """Float sizes of the bottom and top ball caps (how far the ball reaches past T0 and T1)."""
    import math
    r = math.sqrt(b['q'])
    return float(b['T0']) - (float(b['cim']) - r), (float(b['cim']) + r) - float(b['T1'])


def frac_lean(f):
    if f.denominator == 1:
        return f'({f.numerator})'
    return f'({f.numerator} / {f.denominator})'


def emit(seg_name, H, count, order, caps_t, probe=False):
    ns = f'BandGlue_h{H}'
    # The height-H corollaries only exist for the FIRST segment: for a higher segment the island's
    # height theorem consumes the band hypotheses of every segment below it as well.
    corollary = (COROLLARY.format(H=H, count=count, seg_name=seg_name) if H == 1000 else '')
    corollary_doc = (f';\n      * `all_nontrivial_zeros_up_to_height_{H}_of_inputs` / `_of_reduced`: the '
                     f'height-{H}\n        ladder statement from those inputs and the height floor `hγ`'
                     if H == 1000 else '')
    probe_doc = ('\n\n    PROBE (not a lean_lib): it imports the monolith segment `' + seg_name + '`, which this\n'
                 '    island cannot build.  Elaborated with plain `lean` against the monolith build; see\n'
                 '    Probes/BandGlue_Capstone_h280000.lean.' if probe else '')
    L = []
    L.append(f'''/-  {ns}.lean -- K0 + K1 instantiated on a REAL ladder segment: `{seg_name}`
    (the `[{H - 1000 if H > 1000 else 1}, {H}]` segment, {count} Turing bands).
    GENERATED by telperion/examples/zeta_reflection/emit_band_glue.py; DO NOT EDIT BY HAND.{probe_doc}

    `seg` tabulates the segment's {count} bands as `BandGlue.BandData`, parameters copied verbatim
    from each band module's `statement_match`.  The kernel then checks:
      * `seg_edge`: the table's bands cover the segment's boxes (edges equal to `bLo`/`bHi`);
      * `seg_stmt`: every table entry's band statement is the band module's own
        `statement_match` (a mistyped entry would not type-check);
      * `seg_geom`: the K1 ball-cap geometry, with slab heights `capLo i`, `capHi i` (each band's
        own caps rounded up to a multiple of 1e-6; tight on purpose, see emit_band_glue.py).
    and composes them:
      * `boxCert_of_inputs`: a `BandGlue.BoxCert` for box `i` from band `i`'s Arb inputs;
      * `bandHyp_of_inputs`: `{seg_name}.BandHyp` from the per-band Arb inputs (`hLine`, `hArbT`);
      * `bandHyp_of_reduced`: the same from the K1-reduced inputs (on-line zeros, two zero-free
        edge slabs, five enclosures; `hnzl` discharged outright){corollary_doc}.
    `{seg_name}.BandHyp` is, by the capstone's own definitional check, the segment's
    `AllZeros_h280000_Indexed.SegBandHyp`.

    What is still ASSUMED: the per-band inputs themselves (the Arb trust boundary) and `hγ`.
    Nothing here evaluates zeta.  Axioms [propext, Classical.choice, Quot.sound]; no `sorry`.
    conjecture1_proved = False. -/
import Mathlib
import BandGlue
import {seg_name}

open Complex

namespace {ns}

open BandGlue BandGlue.BandData

/-- The {count} Turing bands of `{seg_name}`, in box order (parameters verbatim from each band
    module's `statement_match`). -/
noncomputable def seg : ℕ → BandData := fun i => match i with''')
    for i, b in enumerate(order):
        mod = b['mod']
        args = ', '.join([b['T0_t'], b['T1_t'], b['n_t']] + b['LH_t'])
        L.append(f'  | {i} => ⟨{args},\n      {mod}.cPB, {mod}.RPB, {mod}.hs1PB⟩')
    L.append('  | _ => default')
    L.append('')
    for nm, idx, what in (('capLo', 0, 'bottom'), ('capHi', 1, 'top')):
        L.append(f'/-- The {what}-edge slab heights: band `i`\'s {what} ball cap, rounded up to a multiple of 1e-6. -/')
        L.append(f'noncomputable def {nm} : ℕ → ℝ := fun i => match i with')
        for i, c in enumerate(caps_t):
            L.append(f'  | {i} => {c[idx]}')
        L.append('  | _ => 0')
        L.append('')
    L.append(f'''/-- The table's bands cover the segment's boxes (their edges ARE the box edges `bLo`/`bHi`). -/
theorem seg_edge : ∀ i, i < {count} → (seg i).T0 ≤ {seg_name}.bLo i ∧ {seg_name}.bHi i ≤ (seg i).T1 := by
  intro i hi
  interval_cases i <;> exact ⟨le_rfl, le_rfl⟩

/-- Every table entry's band statement holds: it is the band module's `statement_match`. -/
theorem seg_stmt : ∀ i, i < {count} → (seg i).Stmt (1 / 4000000) (3999999 / 4000000) := by
  intro i hi
  interval_cases i''')
    for b in order:
        L.append(f'  · exact {b["mod"]}.statement_match')
    L.append('')
    L.append(f'''/-- The K1 ball-cap geometry of every band, with slab heights `capLo i`, `capHi i`. -/
theorem seg_geom : ∀ i, i < {count} → (seg i).CapGeom (capLo i) (capHi i) := by
  intro i hi
  interval_cases i''')
    for b, c in zip(order, caps_t):
        L.append(f'  · exact CapGeom.of_sqrt (δ0 := {c[0]}) (δ1 := {c[1]}) {b["T0_t"]} {b["T1_t"]} ({b["cim_t"]}) ({b["q_t"]})\n'
                 f'      rfl rfl rfl rfl\n'
                 f'      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n'
                 f'      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)')
    L.append('')
    L.append(f'''/-- Each box of `{seg_name}` has a band certificate once its band's Arb inputs hold (the
    certificate interface of `BandGlue.BoxCert`, filled by the real `rh_in_box_*` theorems). -/
theorem boxCert_of_inputs (i : ℕ) (hi : i < {count}) (hin : (seg i).Inputs) :
    BoxCert (1 / 4000000) (3999999 / 4000000) ({seg_name}.bLo i) ({seg_name}.bHi i) :=
  BoxCert.of_stmt (seg i) (seg_edge i hi).1 (seg_edge i hi).2 (seg_stmt i hi) hin

/-- **K0 on `{seg_name}`**: the segment's band hypothesis from the per-band Arb inputs
    (`hLine`, `hArbT` of each band theorem), composed through the real `rh_in_box_*` theorems. -/
theorem bandHyp_of_inputs (hin : ∀ i, i < {count} → (seg i).Inputs) : {seg_name}.BandHyp :=
  segBandHyp_of_bands seg seg_edge seg_stmt hin

/-- **K0 + K1 on `{seg_name}`**: the segment's band hypothesis from the reduced per-band inputs
    (on-line zeros, edge clearance at the two edges, five enclosures). -/
theorem bandHyp_of_reduced (hin : ∀ i, i < {count} → (seg i).ReducedInputs (capLo i) (capHi i)) :
    {seg_name}.BandHyp :=
  segBandHyp_of_reduced seg seg_edge seg_stmt seg_geom hin

{corollary}end {ns}
''')
    return '\n'.join(L)


def emit_ladder(K, prefix, counts):
    """The fixed-table K0 composition over segments 0..K-1 of the h(1000 K) capstone: imports the
    K per-segment glue modules `<prefix>BandGlue_h<H>` and composes them into the capstone."""
    H = 1000 * K
    L = [f'''/-  BandGlue_FullTable_h{H}.lean -- K0 (+ K1) against the FULL h{H} capstone, fixed-table form.
    GENERATED by telperion/examples/zeta_reflection/emit_band_glue.py --ladder; DO NOT EDIT BY HAND.

    PROBE (not a lean_lib): it imports the capstone `AllZeros_h{H}_Indexed` and the {K} generated
    per-segment glue modules, all on the monolith side.  `bandTable k` is segment k's band table
    (`BandGlue_h<1000 (k + 1)>.seg`: {sum(counts)} bands, parameters verbatim from the band modules'
    `statement_match`); the theorems below replace the capstone's `hbands` by the per-band Arb
    inputs (`hLine`, `hArbT`) of the {sum(counts)} emitted `rh_in_box_*` theorems, raw or K1-reduced.

    What is still ASSUMED: those per-band inputs (the Arb trust boundary) and `hγ`.  Nothing here
    evaluates zeta.  conjecture1_proved = False. -/
import AllZeros_h{H}_Indexed
import BandGlue''']
    for k in range(K):
        L.append(f'import {prefix}BandGlue_h{1000 * (k + 1)}')
    L.append(f'''
open Complex

namespace BandGlue_FullTable_h{H}

open AllZeros_h{H}_Indexed BandGlue

/-- Segment `k`'s band table. -/
noncomputable def bandTable : ℕ → ℕ → BandData := fun k => match k with''')
    for k in range(K):
        L.append(f'  | {k} => BandGlue_h{1000 * (k + 1)}.seg')
    L.append('  | _ => fun _ => default')
    for nm in ('capLo', 'capHi'):
        L.append(f'''
/-- Segment `k`'s `{nm}` table (K1 slab heights). -/
noncomputable def {nm}Table : ℕ → ℕ → ℝ := fun k => match k with''')
        for k in range(K):
            L.append(f'  | {k} => BandGlue_h{1000 * (k + 1)}.{nm}')
        L.append('  | _ => fun _ => 0')
    L.append(f'''
/-- **K0 per segment**: `SegBandHyp k` from the per-band Arb inputs of segment `k`. -/
theorem segBandHyp_of_band_inputs :
    ∀ k, k < {K} → (∀ i, i < segCount k → (bandTable k i).Inputs) → SegBandHyp k := by
  intro k hk
  interval_cases k''')
    for k in range(K):
        L.append(f'  · exact BandGlue_h{1000 * (k + 1)}.bandHyp_of_inputs')
    L.append(f'''
/-- **K0 + K1 per segment**: `SegBandHyp k` from the K1-reduced per-band inputs of segment `k`. -/
theorem segBandHyp_of_reduced_inputs :
    ∀ k, k < {K} → (∀ i, i < segCount k →
      (bandTable k i).ReducedInputs (capLoTable k i) (capHiTable k i)) → SegBandHyp k := by
  intro k hk
  interval_cases k''')
    for k in range(K):
        L.append(f'  · exact BandGlue_h{1000 * (k + 1)}.bandHyp_of_reduced')
    L.append(f'''
/-- **K0 against the full capstone, fixed-table form**: every zero of ζ with `0 < Im ρ ≤ {H}`
    is on the line, given the per-band Arb inputs of all {sum(counts)} emitted band theorems and
    the height floor. -/
theorem all_nontrivial_zeros_up_to_height_{H}_of_band_inputs
    (hin : ∀ k, k < {K} → ∀ i, i < segCount k → (bandTable k i).Inputs)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → ρ.re = 1 / 2 :=
  all_nontrivial_zeros_up_to_height_{H} (fun k hk => segBandHyp_of_band_inputs k hk (hin k hk)) hγ

/-- **K0 + K1 against the full capstone, fixed-table form**: the same from the K1-reduced
    per-band inputs (on-line zeros, two zero-free edge slabs, five enclosures). -/
theorem all_nontrivial_zeros_up_to_height_{H}_of_reduced_inputs
    (hin : ∀ k, k < {K} → ∀ i, i < segCount k →
      (bandTable k i).ReducedInputs (capLoTable k i) (capHiTable k i))
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → ρ.re = 1 / 2 :=
  all_nontrivial_zeros_up_to_height_{H} (fun k hk => segBandHyp_of_reduced_inputs k hk (hin k hk)) hγ

end BandGlue_FullTable_h{H}

#print axioms BandGlue_FullTable_h{H}.segBandHyp_of_band_inputs
#print axioms BandGlue_FullTable_h{H}.segBandHyp_of_reduced_inputs
#print axioms BandGlue_FullTable_h{H}.all_nontrivial_zeros_up_to_height_{H}_of_band_inputs
#print axioms BandGlue_FullTable_h{H}.all_nontrivial_zeros_up_to_height_{H}_of_reduced_inputs
''')
    return '\n'.join(L)


COROLLARY = '''/-- The height-{H} ladder statement from the per-band Arb inputs and the height floor. -/
theorem all_nontrivial_zeros_up_to_height_{H}_of_inputs
    (hin : ∀ i, i < {count} → (seg i).Inputs)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → ρ.re = 1 / 2 :=
  {seg_name}.all_nontrivial_zeros_up_to_height_{H}_of_bands (bandHyp_of_inputs hin) hγ

/-- The height-{H} ladder statement from the K1-reduced per-band inputs and the height floor. -/
theorem all_nontrivial_zeros_up_to_height_{H}_of_reduced
    (hin : ∀ i, i < {count} → (seg i).ReducedInputs (capLo i) (capHi i))
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → ρ.re = 1 / 2 :=
  {seg_name}.all_nontrivial_zeros_up_to_height_{H}_of_bands (bandHyp_of_reduced hin) hγ

'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('zdir')
    ap.add_argument('H', type=int)
    ap.add_argument('out')
    ap.add_argument('--ladder', action='store_true',
                    help='emit the fixed-table composition of segments 0..H/1000-1 instead')
    ap.add_argument('--prefix', default='', help='module prefix of the per-segment glue (--ladder)')
    ap.add_argument('--res', type=int, default=1000000)
    ap.add_argument('--probe', action='store_true')
    a = ap.parse_args()
    zdir = Path(a.zdir)
    if a.ladder:
        K = a.H // 1000
        counts = [parse_segment(zdir, 1000 * (k + 1))[1] for k in range(K)]
        Path(a.out).write_text(emit_ladder(K, a.prefix, counts))
        print(f'wrote {a.out}: {K} segments, {sum(counts)} bands')
        return
    seg_name, count, order = parse_segment(zdir, a.H)
    caps_t = []
    for b in order:
        if (b['sig0'], b['sig1']) != (Fraction(1, 4000000), Fraction(3999999, 4000000)):
            sys.exit(f'{b["mod"]}: unexpected strip')
        dlo, dhi = band_caps(b, a.res)
        if not cap_check(b, dlo, dhi):
            sys.exit(f'{b["mod"]}: cap geometry fails; caps {caps(b)}')
        caps_t.append((frac_lean(dlo), frac_lean(dhi)))
    cs = [c for b in order for c in caps(b)]
    print(f'{seg_name}: {count} bands; caps min {min(cs):.6f} max {max(cs):.6f}; rounded up to 1/{a.res}')
    Path(a.out).write_text(emit(seg_name, a.H, count, order, caps_t, a.probe))
    print(f'wrote {a.out}')


if __name__ == '__main__':
    main()
