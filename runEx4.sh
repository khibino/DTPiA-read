#!/bin/sh

set -e

exe=Exercise4

errs='
s4err.lam
'

srcs='
s1.lam
s2.lam
s3.lam
s4.lam
'

for f in $errs; do
    echo $f
    ./$exe < $f || true
done

for f in $srcs; do
    echo $f
    ./$exe < $f
done
