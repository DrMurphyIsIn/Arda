#!/bin/sh
cd /private/tmp/claude-0/crux2/kappa-certify/builder
P=/usr/bin/python3
( $P udomain_galerkin.py 249/256 dh even 10,20,30,40 384 4 ud_dh_a249_even.json > log_ud_dh_a249_even.txt 2>&1 ;
  $P udomain_galerkin.py 249/256 dh odd 10,20,30,40 384 4 ud_dh_a249_odd.json > log_ud_dh_a249_odd.txt 2>&1 ) &
( $P udomain_galerkin.py 307/256 dh even 10,20,30,40 384 4 ud_dh_a307_even.json > log_ud_dh_a307_even.txt 2>&1 ;
  $P udomain_galerkin.py 307/256 dh odd 10,20,30,40 384 4 ud_dh_a307_odd.json > log_ud_dh_a307_odd.txt 2>&1 ) &
( $P udomain_galerkin.py 472/256 dh even 10,20,30,40,50 384 4 ud_dh_a472_even.json > log_ud_dh_a472_even.txt 2>&1 ;
  $P udomain_galerkin.py 472/256 dh odd 10,20,30,40,50 384 4 ud_dh_a472_odd.json > log_ud_dh_a472_odd.txt 2>&1 ;
  $P udomain_galerkin.py 472/256 zeta even 20,40,60 512 4 ud_a472_even.json > log_ud_a472_even.txt 2>&1 ) &
wait
