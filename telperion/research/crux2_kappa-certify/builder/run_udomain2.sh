#!/bin/sh
cd /private/tmp/claude-0/crux2/kappa-certify/builder
P=/usr/bin/python3
$P udomain_galerkin.py 307/256 zeta even 80,90,100,110,120 768 4 ud_a307_even_hi.json > log_ud_a307_even_hi.txt 2>&1 &
$P udomain_galerkin.py 307/256 zeta odd 80,90,100,110,120 768 4 ud_a307_odd_hi.json > log_ud_a307_odd_hi.txt 2>&1 &
$P udomain_galerkin.py 307/256 zeta even 90 768 8 ud_a307_even_p8.json > log_ud_a307_even_p8.txt 2>&1 &
wait
