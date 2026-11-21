#!/bin/bash
# negative/positive controls with encoding X + kissat: run_ctl.sh JOBS name1 name2 ...  (names of out/ctl/*.jsonl)
cd "$(dirname "$0")"
J=$1; shift
for name in "$@"; do
  n=$(echo $name | cut -d_ -f2); k=$(echo $name | cut -d_ -f3)
  nice -n 10 ${PY:-python3} xrun.py $n $k out/ctl/$name.jsonl out/ctl/x_$name.jsonl --jobs $J --tl 4000 > logs/ctl_$name.log 2>&1
  echo "$name: $(tail -1 logs/ctl_$name.log)"
done
