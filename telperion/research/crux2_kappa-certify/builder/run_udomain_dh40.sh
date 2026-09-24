#!/bin/sh
cd /private/tmp/claude-0/crux2/kappa-certify/builder
P=/usr/bin/python3
$P udomain_galerkin.py 472/256 dh even 70,90,110 512 4 ud_dh_a472_even_hi.json > log_ud_dh_a472_even_hi.txt 2>&1 &
$P udomain_galerkin.py 472/256 dh odd 70,90,110 512 4 ud_dh_a472_odd_hi.json > log_ud_dh_a472_odd_hi.txt 2>&1 &
wait
