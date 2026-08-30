# bg_flag_discharge — the Brualdi-Goldwasser route-(b) walk-count `m_2` cut (kernel-gated)

Emitter-generated, Mathlib-only frozen Lean (`lean/BGFlagDischarge.lean`, kernel-checked by
`telperion-lean-e2e` via `lake build`; regenerated stdlib-only by `generate.py` from a frozen exact-rational
dual). `conjecture1_proved = False` — this is **not** a proof of Brualdi-Goldwasser.

## What it certifies

Route (b) bounds the matching free-energy growth rate `rho* = lim_n max_T (per(L)/prod deg)^(1/n) = 1.2276458`
by a walk-moment functional. The mass-transport flag-LP **dual** is an antisymmetric edge-discharge potential
`w(d,e) = -w(e,d)`; with scalars `(b0,b1,b2)` it yields a per-vertex inequality

    2 x^2 - q  >=  b0 + b1 d + b2 x + sum_{a~v} w(d, d_a),     x = S_v/d_v, q = Q_v/d_v^2,

which **telescopes** over any tree (`sum_v sum_{a~v} w(d_v,d_a) = 0`) and, with the handshake
`sum d = 2n-2`, assembles into the certified lower bound

    m_2(T)  >=  b0 + b1*(2 - 2/n) + b2 * m_1(T),     m_k = (1/n) Tr N^{2k},  N = D^{-1/2} A D^{-1/2}

for every tree of maximum degree <= 7. Here `b0 = -1937/3600`, `b1 = 13/360`, `b2 = 1081/720`, and the
`-2 b1 / n` term is the surface correction of the finite-tree / density gap. Each emitted theorem is one
rational per-type inequality (`2x^2-q >= ...`) the Lean kernel re-checks by `norm_num`, tight at the
extremal length-2-arm caterpillar (the profile with slack 0).

## How it was found (and its honest ceiling)

The dual was derived offline by `FlagDischargeCertificate.from_flag_lp` (a mass-transport LP over the
degree-neighbourhood distribution, numpy/scipy), then **frozen as exact rationals** so generation +
drift-check need only the stdlib. The certificate is **one finite level of a convergent hierarchy**: the
walk-count `m_2` cut is the load-bearing constraint of the route-(b) moment-SDP, and this discharge dual
certifies it for bounded degree. It is NOT the full density bound — `log rho*` is a thermodynamic limit that
no finite local relaxation reaches (see `docs/BG_WALK_COUNT_SUBPROBLEM.md`, W5-W20, for the full arc: the
exact route is an infinite-tree variational / concavity argument, reduced there to a single open analytic
step). `conjecture1_proved = False`.

## Files

- `generate.py` — reconstructs the certificate from the frozen rational dual and emits `lean/`; `--check`
  is the drift gate (stdlib-only).
- `lean/BGFlagDischarge.lean` — the emitted `norm_num` atoms (Mathlib-only), kernel-built by `lake build`.
- `src/telperion/flag_discharge.py` — the `FlagDischargeCertificate` emitter (stdlib-only).
- `docs/BG_WALK_COUNT_SUBPROBLEM.md` + `docs/bg_*.py` — the full W2-W20 research record and reproductions.
