#!/bin/sh
# BUILDER: regenerate the x = 11.006 Schur cores (even + odd) from the saved wa3 matrices with the radius-inflation fix.
cd /private/tmp/claude-0/crux2/kappa-certify
PYTHONPATH=/private/tmp/claude-0/crux2/kappa-certify
export PYTHONPATH
date
/usr/bin/python3 builder/schur_core_file_fixed.py M_wa3_a307_odd_odd.txt 4.4579e-45 8 60 builder/schur_core_x11_odd_fixed.json
date
/usr/bin/python3 builder/schur_core_file_fixed.py M_wa3_a307_even_even.txt 6.6018e-49 8 60 builder/schur_core_x11_even_fixed.json
date
