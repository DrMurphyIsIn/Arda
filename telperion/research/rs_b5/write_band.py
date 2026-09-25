# UNTRUSTED writer: band_<tag>.json -> RS5_Band_<Name>_C<j>.lean (chunks: data + kernel decides)
# and RS5_Band_<Name>.lean (glue + headline).  Usage: write_band.py <tag> <Name> <chunk_size>
import sys, json, os
ISL = '/Users/peterwmurphy/arda-rs-b5/telperion/examples/zeta_reflection/lean'
SCR = os.path.dirname(os.path.abspath(__file__))


def lean_sample(s):
    c = s['cert']
    return '⟨' + f"{s['tn']}, {s['tq']}, {s['E']}, ⟨" + ', '.join(str(x) for x in c) + '⟩⟩'


def rat(s):
    return f"({s['tn']} / {1 << s['tq']} : ℝ)"


def chunk_file(name, j, S, rep):
    K = sum(1 for a, b in zip(S, S[1:]) if a['pos'] != b['pos'])
    mod = f'RS5_Band_{name}_C{j}'
    ns = f'RS5.Band{name}.C{j}'
    lo, hi = S[0], S[-1]
    txt = f'''/-  {mod}.lean -- lane B5: chunk {j} of the band certificate {name} ({rep['T0']} .. {rep['T1']}).

    {len(S)} dyadic sample heights from t = {lo['tn']}/2^{lo['tq']} to t = {hi['tn']}/2^{hi['tq']}, each with an RS4
    certificate (P = 64) and the seam margin (13/5) E / 2^64 >= (13/5) t^(-3/4).  Emitted by the UNTRUSTED
    pipeline scratchpad/b5/emit5.py; re-checked here by `decide +kernel` (`RS5.bandOK`).
    Certified: {K} adjacent sign changes, hence `BandZeros lo hi {K}`.

    conjecture1_proved = False.
-/
import RS5_Band

open Complex

namespace {ns}

open RS5

noncomputable def s0 : Sample :=
  {lean_sample(S[0])}

noncomputable def rest : List Sample := [
''' + ',\n'.join('  ' + lean_sample(s) for s in S[1:]) + f''']

/-- The kernel accepts the chunk ({len(S)} samples). -/
theorem ok : bandOK (s0 :: rest) = true := by decide +kernel

theorem count : chgBy Sample.pos (s0 :: rest) = {K} := by decide +kernel

theorem last_eq : (lastOf s0 rest).tn = {hi['tn']} ∧ (lastOf s0 rest).tq = {hi['tq']} := by decide +kernel

theorem t0_eq : s0.t = {rat(lo)} := by
  show ((({lo['tn']} : ℕ) : ℝ)) / 2 ^ ({lo['tq']} : ℕ) = {rat(lo)}
  norm_num

theorem t1_eq : (lastOf s0 rest).t = {rat(hi)} := by
  unfold Sample.t
  rw [last_eq.1, last_eq.2]
  norm_num

/-- **{K} distinct on-line zeros of `riemannZeta` in this chunk.** -/
theorem zeros : BandZeros {rat(lo)} {rat(hi)} {K} := by
  have h := bandZeros_of_ok s0 rest ok
  rw [count, t0_eq, t1_eq] at h
  exact h

end {ns}
'''
    open(os.path.join(ISL, mod + '.lean'), 'w').write(txt)
    return mod, K, lo, hi


def main():
    tag, name, csz = sys.argv[1], sys.argv[2], int(sys.argv[3])
    d = json.load(open(os.path.join(SCR, f'band_{tag}.json')))
    rep, S = d['report'], d['samples']
    T0, T1, K, tq = rep['T0'], rep['T1'], rep['K'], rep['tq']
    assert S[0]['tn'] == T0 << tq and S[-1]['tn'] == T1 << tq
    n = len(S)
    nch = max(1, round((n - 1) / csz))
    cuts = [round(i * (n - 1) / nch) for i in range(nch + 1)]
    chunks = []
    for j in range(nch):
        chunks.append(chunk_file(name, j, S[cuts[j]:cuts[j + 1] + 1], rep))
    assert sum(c[1] for c in chunks) == K
    mod = f'RS5_Band_{name}'
    imports = '\n'.join(f'import {c[0]}' for c in chunks)
    # glue expression
    expr = f'Band{name}.C0.zeros'
    for j in range(1, nch):
        expr = f'({expr}).glue (by norm_num) (by norm_num) Band{name}.C{j}.zeros'
    Ks = ' + '.join(str(c[1]) for c in chunks)
    txt = f'''/-  {mod}.lean -- lane B5: the band certificate on [{T0}, {T1}] (headline; glues {nch} kernel-checked chunks).

    {n} dyadic sample heights t_i = tn_i / 2^{tq}, t_0 = {T0}, t_k = {T1}, emitted by the UNTRUSTED pipeline
    scratchpad/b5/emit5.py and re-checked chunk by chunk by `decide +kernel` (`RS5.bandOK`), chunks
    {', '.join(c[0] for c in chunks)}.  Per-chunk sign-change counts {Ks} = {K}.

    Result: {K} DISTINCT zeros of Mathlib's `riemannZeta` on the critical line with ordinates in ({T0}, {T1}).
    Untrusted cross-check: mpmath N({T1}) - N({T0}) = {rep['mpmath_count']}, so this lower count is
    {'SHARP (equals N(T1) - N(T0))' if rep['sharp'] else 'NOT sharp'} numerically.  The matching UPPER count (that there
    are no other zeros, on or off the line, in the band) is NOT proved on this branch: see `RS5_Band`
    (argument principle / Turing count, branches cl/arb3-h1000 #613 and cl/arb4 #620).

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/
{imports}

open Complex

namespace RS5.Band{name}

open RS5

/-- **{K} distinct on-line zeros in ({T0}, {T1})** (`BandZeros`: strictly increasing list, Lambda = 0 and
    riemannZeta = 0 at 1/2 + i x). -/
theorem zeros : BandZeros {T0} {T1} {K} :=
  ({expr}).mono (by norm_num) (by norm_num)

/-- **{K} distinct zeros of `riemannZeta` on the critical line with ordinates in ({T0}, {T1}).** -/
theorem zeta_zeros : ∃ xs : List ℝ, xs.length = {K} ∧ xs.IsChain (· < ·) ∧
    (∀ x ∈ xs, ({T0} : ℝ) < x ∧ x < {T1}) ∧
    (∀ x ∈ xs, riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := zeros.zeta

/-- The same as a `Finset` of card {K}. -/
theorem zeta_zeros_finset : ∃ S : Finset ℝ, S.card = {K} ∧
    ∀ x ∈ S, ({T0} : ℝ) < x ∧ x < {T1} ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0 := zeros.finset

/-- The `hLine` antecedent of `TuringBand.BandStatement _ _ {T0} {T1} {K} ...`, verbatim shape. -/
theorem hLine : ∃ xs : List ℝ, xs.length = {K} ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, ({T0} : ℝ) ≤ t ∧ t ≤ {T1}) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := zeros.hLine

end RS5.Band{name}
'''
    open(os.path.join(ISL, mod + '.lean'), 'w').write(txt)
    print(mod, n, K, [(c[0], c[1]) for c in chunks])


if __name__ == '__main__':
    main()
