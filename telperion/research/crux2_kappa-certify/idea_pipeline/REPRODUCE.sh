#!/bin/sh
# kappa-certify reproduction (python-flint 0.6.0, mpmath 1.3.0, /usr/bin/python3 3.9; ~1-3 h total on 1 core)
# conjecture1_proved = False.
cd "$(dirname "$0")"
PY=/usr/bin/python3
$PY check_ef.py                                   # explicit-formula normalization vs 2000 zeros
$PY certify.py 0.8 200 200 9e-18 1.1e-14 256      # Zhu's a=0.8 reproduced (>= 9e-18 / 1.1e-14)
$PY run_cert.py 249/256 560 450 256 a249_T560     # a=0.9727: even >= 4.395e-28 (odd fails at T#=560 -- see notes)
$PY -c "import run_cert; run_cert.run('249/256', 800.0, 620, 256, tag='a249_T800_odd', sectors=('odd',))"
$PY -c "import run_cert; run_cert.run('133/128', 2300.0, 1720, 256, tag='a133_T2300_even', sectors=('even',))"
$PY -c "import run_cert; run_cert.run('133/128', 2300.0, 1720, 256, tag='a133_T2300_odd', sectors=('odd',))"
$PY -c "import run_cert; run_cert.run('249/256', 200.0, 140, 256, tag='DH_a249_T200', kind='dh')"   # D control
$PY sep_cert.py 40 60 1024                        # zeta PD vs D indefinite at x=40
$PY upper_bound.py 249/256 200 512; $PY upper_bound.py 133/128 200 512   # certified upper bounds
$PY -c "import certify_wa; certify_wa.run('249/256', 0.34, 121.0, 50.0, 740, 256, sectors=('even',))"  # new reduction
$PY -c "import certify_wa; certify_wa.run('249/256', 0.34, 400.0, 50.0, 900, 256, sectors=('odd',))"
$PY schur_core.py 8; $PY schur_core.py 8 odd
$PY emit_lean_core.py schur_core_k8.json lean/KappaWindowCore.lean even
$PY emit_lean_core.py schur_core_k8_odd.json lean/KappaWindowCoreOdd.lean odd
# Lean (single-file elaboration on the li_positivity island; never lake build):
#   cd telperion/examples/li_positivity/lean && lake env lean <path>/lean/KappaWindowCore.lean   (etc.)
