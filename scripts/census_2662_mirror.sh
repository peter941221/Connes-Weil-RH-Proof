#!/bin/bash
# Record-2662/2663: file-level olean census across candidate WSL workspaces.
# Finds which workspace holds the green PanelTrueBall2662 batch and its
# composition module. No shell variables cross the wsl.exe boundary: this
# file is piped in via `tr -d "\r" | bash`.
for d in /home/peter/rh /home/peter/projects/Connes-Weil-RH-Proof \
         /home/peter/verify-2628-current /home/peter/batch2628 \
         /home/peter/batch2632 /home/peter/cwr-current-20261002 \
         /home/peter/verify-2622 /home/peter/verify-2623 \
         /home/peter/verify-2617-controlled /home/peter/rh-cert \
         /home/peter/rh-lean-worktree; do
  s=$(ls "$d"/ConnesWeilRH/Dev/ 2>/dev/null | grep -c PanelTrueBall2662)
  o=$(ls "$d"/.lake/build/lib/lean/ConnesWeilRH/Dev/ 2>/dev/null | grep -c "PanelTrueBall2662P.*olean")
  c=$(ls "$d"/.lake/build/lib/lean/ConnesWeilRH/Dev/ 2>/dev/null | grep -c "PanelComposition2662.olean")
  echo "$d src=$s olean=$o composition=$c"
done

W1=/home/peter/projects/Connes-Weil-RH-Proof
W2=/mnt/c/Projects/Connes-Weil-RH-Proof
echo "=== md5 all 190 (projects vs windows) ==="
bad=0
for i in $(seq -w 0 189); do
  f="C1RouteAPanelTrueBall2662P$i.lean"
  a=$(md5sum "$W1/ConnesWeilRH/Dev/$f" 2>/dev/null | cut -d' ' -f1)
  b=$(md5sum "$W2/ConnesWeilRH/Dev/$f" 2>/dev/null | cut -d' ' -f1)
  if [ "$a" != "$b" ]; then echo "DIFF $f $a $b"; bad=$((bad + 1)); fi
done
echo "md5 mismatches: $bad / 190"
for f in C1RouteAPanelComposition2662.lean C1RouteAComplexPanelTable2655P109.lean; do
  a=$(md5sum "$W1/ConnesWeilRH/Dev/$f" 2>/dev/null | cut -d' ' -f1)
  b=$(md5sum "$W2/ConnesWeilRH/Dev/$f" 2>/dev/null | cut -d' ' -f1)
  [ "$a" = "$b" ] && echo "OK   $f $a" || echo "DIFF $f $a $b"
done
echo "=== oleans present (projects) ==="
ls "$W1/.lake/build/lib/lean/ConnesWeilRH/Dev/" | grep -E "^C1RouteAPanelComposition2662\.olean$|^C1RouteAComplexPanelTable2655P109\.olean$"