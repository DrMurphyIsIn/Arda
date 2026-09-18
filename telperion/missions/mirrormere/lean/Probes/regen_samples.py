"""Regenerate missions/mirrormere/lean/Probes/MMWeilGramCertSamples.lean (see the D2 design memo)."""
import sympy as sp
from telperion.emit_weil_form_enclosure import *
from telperion.emit_interval_gram_inertia import *
q = sp.Rational
class F:
    def __init__(s, i): s.instances = i
class I:
    def __init__(s, n, p): s.lean_name, s.payload = n, p

HEADER = '''/-
  Probes.MMWeilGramCertSamples -- COMPILE SAMPLES of the two D2 certificate tools built for
  MM_weil_gram_trace: telperion/src/telperion/emit_weil_form_enclosure.py (kind
  weil_form_enclosure) and emit_interval_gram_inertia.py (kind interval_gram_inertia).

  Every theorem below was EMITTED, not hand-written; the generator is recorded in the design
  memo telperion/docs/MM_mm-d2-weil-gram-trace_DESIGN_2026-09-18.md section 8, and the script
  that produced this file is Probes/regen_samples.py next to it.  The numbers are
  ILLUSTRATIVE (hand-chosen intervals), NOT Weil-form data of any test family: the point of the
  file is that the emitted Lean shapes elaborate and their tactics close at the mirrormere pin
  (leanprover/lean4:v4.32.0).  Outside defaultTargets, no sorry, no RH content.
  conjecture1_proved = False.
-/
import Mathlib
'''
print(HEADER)

wf = weil_form_enclosure_certificate(WeilFormData(
    label="0,1:re", support_radius=q("3/2"),
    arch_lo=q("11/10"), arch_hi=q("6/5"),
    terms=(PrimeTermInterval(2, q("1/10"), q("11/100")),
           PrimeTermInterval(3, q("1/20"), q("6/100")),
           PrimeTermInterval(4, q("1/40"), q("3/100")))))
print(WeilFormEnclosureEmitter().emit_body(F([I("sample_weil_form_01_re", wf)]), None)[0])

m = IntervalHermitian(k=3,
    diag=((q("-1"), q("-1/2")), (q("-1"), q("-1/2")), (q("-2"), q("-1"))),
    off={(0,1): ((q("-1/100"), q("1/100")), (q("-1/100"), q("1/100"))),
         (0,2): ((q("-1/100"), q("1/100")), (q("-1/100"), q("1/100"))),
         (1,2): ((q("-1/100"), q("1/100")), (q("-1/100"), q("1/100")))})
neg = interval_gram_inertia_certificate(GramInertiaData(
    label="illustrative 3x3, witness (1, i, 1+i)", matrix=m, mode="negative",
    witness=((q(1), q(0)), (q(0), q(1)), (q(1), q(1)))))
print(IntervalGramInertiaEmitter().emit_body(F([I("sample_gram_negative_dir", neg)]), None)[0])

dm = IntervalHermitian(k=3,
    diag=((q("3/10"), q("4/10")), (q("3/10"), q("4/10")), (q("3/10"), q("4/10"))),
    off={(0,1): ((q("-1/20"), q("1/20")), (q("-1/20"), q("1/20"))),
         (0,2): ((q("-1/20"), q("1/20")), (q("-1/20"), q("1/20"))),
         (1,2): ((q("-1/20"), q("1/20")), (q("-1/20"), q("1/20")))})
dom = interval_gram_inertia_certificate(GramInertiaData(
    label="illustrative 3x3, dominance", matrix=dm, mode="dominance"))
print(IntervalGramInertiaEmitter().emit_body(F([I("sample_gram_dominance", dom)]), None)[0])
