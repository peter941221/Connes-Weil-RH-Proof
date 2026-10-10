#!/bin/bash
# Record-2663 mirror sync: copy files from the Windows tree into the WSL
# build mirror when they are missing OR byte-different (md5).  The file
# list is the transitive import closure produced by closure_2663.py.
WIN=/mnt/c/Projects/Connes-Weil-RH-Proof
WSL=/home/peter/projects/Connes-Weil-RH-Proof
LIST="$WIN/results/closure_2663.txt"
copied=0
total=0
while IFS= read -r f; do
  [ -z "$f" ] && continue
  total=$((total+1))
  if [ ! -f "$WSL/$f" ]; then
    mkdir -p "$WSL/$(dirname "$f")"
    cp "$WIN/$f" "$WSL/$f"
    echo "COPY-MISSING $f"
    copied=$((copied+1))
  else
    a=$(md5sum < "$WIN/$f" | cut -d' ' -f1)
    b=$(md5sum < "$WSL/$f" | cut -d' ' -f1)
    if [ "$a" != "$b" ]; then
      cp "$WIN/$f" "$WSL/$f"
      echo "COPY-DIFF $f"
      copied=$((copied+1))
    fi
  fi
done < "$LIST"
echo "SYNC-DONE total=$total copied=$copied"