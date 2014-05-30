#!/bin/sh -e
input=$1
sail=../sail.native

output1=`mktemp  --suffix=.sail`
echo Pretty-printing $input
$sail -verbose $input > $output1

output2=`mktemp  --suffix=.sail`
echo Pretty-printing pretty-printed
$sail -verbose $output1 > $output2

diff -u $output1 $output2 && \
  (rm -f $output1 $output2; echo Idempotence: ok)
