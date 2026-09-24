#!/bin/sh
cd /private/tmp/claude-0/crux2/kappa-certify/builder
P=/usr/bin/python3
( $P udomain_galerkin.py 249/256 zeta even 20,30,40,50,60 512 4 ud_a249_even.json > log_ud_a249_even.txt 2>&1 ;
  $P udomain_galerkin.py 249/256 zeta odd 20,30,40,50,60 512 4 ud_a249_odd.json > log_ud_a249_odd.txt 2>&1 ) &
( $P udomain_galerkin.py 133/128 zeta even 20,30,40,50,60 512 4 ud_a133_even.json > log_ud_a133_even.txt 2>&1 ;
  $P udomain_galerkin.py 133/128 zeta odd 20,30,40,50,60 512 4 ud_a133_odd.json > log_ud_a133_odd.txt 2>&1 ) &
( $P udomain_galerkin.py 307/256 zeta even 20,30,40,50,60,70 512 4 ud_a307_even.json > log_ud_a307_even.txt 2>&1 ;
  $P udomain_galerkin.py 307/256 zeta odd 20,30,40,50,60,70 512 4 ud_a307_odd.json > log_ud_a307_odd.txt 2>&1 ) &
wait
