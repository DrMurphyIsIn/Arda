# The Telperion Registry Explorer

`conjecture1_proved = False`. Start there, because this whole directory exists to say
that sentence in pictures without ever contradicting it.

## What this is

A single static web page, `docs/explorer/index.html`, that shows what the Telperion
missions registry currently holds, with the reverse-Dyson quasicrystal program
(campaign `mirrormere`) in front. It is modelled on the presentation of Alvaro
Lozano-Robledo's [Riemann Hypothesis Explorer](https://alozanoroble.github.io/riemann-hypothesis-explorer/)
(CC BY 4.0): one page, a row of tabs, lettered steps inside each tab, plots computed live
in the browser, and plain "What is known" and "Compute it yourself" sections at the end. We
borrowed the shape and the manners, not the code; the footer says so.

The page has seven tabs.

1. **The quasicrystal.** What a Fourier quasicrystal is, the Guinand-Weil dual comb
   picture, Dyson's 2009 suggestion, the reverse-Dyson framing, the axiom variants
   A / B / Bm / C / D, and a box that separates what the campaign claims (the Weil
   criterion in the kernel, both directions; the two-parameter wall; the free region; the
   Theta face) from what it does not (that either side of any equivalence holds).
2. **The zoo.** The falsification matrix as a heat table, object by clause, with the
   recorded detail on hover, straight from `examples/quasicrystal/zoo_data/zoo_verdicts.json`.
   Then the prime comb and its diffraction sum, live, with sliders for how many prime
   powers to include and how high to look; and the Davenport-Heilbronn inventory with its
   off-line zeros drawn beside zeta's ordinates as the negative control.
3. **The wall.** The two-parameter map in `(c, lam)`: the unconditional strip
   `lam <= 3/2000`, the sharp envelope beyond which every centre is free, the
   ladder-certified band that is conditional on `WindowOnLine`, and the residual, which is
   RH. Then `F(c, lam)` computed live from the bundled ordinates with an optional fictitious
   off-line zero to show what a violation would look like, and the Theta face with a width
   slider to show the heat monotonicity.
4. **Li face.** A bar chart of `lambda_N` computed live as the paired zero sum plus a smooth
   tail, with rungs 0..4 highlighted as kernel and hypothesis-free, the 20 Arb-conditional
   certified lower bounds drawn as ticks, and the exchange rate `n + 1 <= 2 pi (T - 1/2)`
   drawn against the heights that exist.
5. **The registry.** Status counts per campaign, a dependency graph in SVG coloured by
   status, and a card per node with its title, kind, verbatim statement (hypotheses
   included), artifact link into GitHub, `closure_clean`, CI coverage label, and the
   readback with its auditor, date, and its independence label as the registry records it ("self-attested", or "judge-verified" once a Comparator run is recorded), plus the grant digest, judge run and required CI run when present. The "proved only" filter
   is on by default.
6. **What is known.** A plain list of what the registry holds, followed by the honesty
   footer: RH is not proved, every goal node is a draft, everything Arb-conditional is not a
   kernel theorem, every plot is a float model, every audit carries the independence label the registry records.
7. **Compute it yourself.** How to run `telperion mission verify`, build an island with
   `lake build`, read the axiom guard, run the Comparator, run the zoo, and rebuild this
   page.

## How it is built

`build.py` does three things and nothing else.

* It loads the registry through `telperion.missions.registry.load_universe`, the same
  loader the verify gate uses. It never parses a TOML file itself, so it cannot disagree
  with `mission status` about what a node's status is. For each node it records the status,
  kind, title, dependencies (qualified as `campaign:slug`), artifact path and GitHub URL,
  `closure_clean`, the verbatim statement from `missions/<campaign>/lean/Statements/`, the
  readback, and a CI coverage label from `telperion.missions.coverage` ("module-covered"
  means a runnable CI step is statically known to compile the artifact's module; it does not
  mean that step passed on the current commit).
* It gathers the plot inputs: the zoo verdicts and the DH inventory verbatim; the first 2000
  zero ordinates from `research/zeros2000.json` (mpmath `zetazero`, a float model, because
  the certified Arb ladder needs python-flint and this build does not require it); the 20
  `hlo` bounds parsed out of `examples/li_positivity/lean/LiPositivity.lean`; and the sharp
  envelope of E6Bridge16 evaluated on a grid of widths, with `primeAbs(lam)` summed over the
  prime powers up to two million. The test suite checks those `primeAbs` values against the
  numbers printed in the Lean docstring.
* It inlines `src/index.html`, `src/explorer.css`, `src/explorer.js`, and the two JSON
  files into one HTML file. No CDN, no fonts fetched, no library. Plots are plain canvas;
  the dependency graph is plain SVG. Light and dark follow `prefers-color-scheme`, with a
  toggle that remembers itself in `localStorage`.

The build is deterministic: no timestamps, no git metadata. That is what makes
`build.py --check` meaningful. It rebuilds in memory and compares bytes against
`explorer/data/registry.json`, `explorer/data/plots.json` and `docs/explorer/index.html`;
any difference means the committed page is stale and the command exits 1.
`tests/test_explorer_build.py` runs the same comparison under pytest, so a registry edit
without a rebuild fails CI the way an emitter island's `generate.py --check` does.

```
cd telperion
python explorer/build.py             # rebuild
python explorer/build.py --check     # stale?
python -m pytest tests/test_explorer_build.py -q
```

Publishing is a repository setting, not something the build does: GitHub Pages, deploy
from branch `main`, folder `/docs`, and the page appears at `/explorer/`.

## What it must never claim

The page is downstream of the registry and must stay that way.

* No status is invented. If the registry says `open`, the page says `open`, even when the
  node's title says the theorem is done and the artifact is linked.
* No conditional or Arb-certified result is shown as a proof. The Li rung certificates enter
  the kernel with an `hlo` hypothesis and are labelled "Arb-conditional". The height-4000
  ladder composition is conditional on Arb band hypotheses and says so. The DH inventory and
  every zoo verdict are Arb / interval computations and carry that label on the tab. A node
  whose slug or title names a condition shows a badge and its hypotheses are one click away
  in the verbatim statement.
* No number computed on the page is presented as an enclosure. Every plot is a float model
  over a truncated list of ordinates that are themselves a float model, and each readout
  says so.
* No audit is presented as independent. Every readback recorded to date was written by the
  same session family that wrote the node unless a Comparator judge run is recorded; the card shows the label the registry stores.
* The goal nodes stay drafts on the page because they are drafts in the registry. The
  MIRRORMERE goal is RH by theorem (`MM_zeta_comb_membership_iff_rh`), which is exactly why
  it cannot be anything else.
* The sentence `conjecture1_proved = False` appears in the banner, the data files, the
  footer, and this README. The build refuses to emit a page that has lost it.

If you add a plot, label its trust level in the readout. If you add a tab, put the
non-claims in it before the claims. If you are tempted to colour a conditional node green,
read the campaign manifests first: they were written by people who wanted this page to
exist and did not want it to lie.
