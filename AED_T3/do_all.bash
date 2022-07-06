#! /bin/bash

for n in {100..3}; do
  if [ -e stop_request ]; then
    exit 0
  fi
  f=$(printf %04d $n)
  export TIMEFORMAT="$n done in %3Us"
  if [ ! -e $f ]; then
    time ./A03 -x $n >$f
  fi
done
echo All done
