OUT=/tmp/recon2676e.txt
: > $OUT
for W in /home/peter/verify-2628-current /home/peter/cwr-current-20261002 /home/peter/verify-2617-controlled /home/peter/cwrh-native /home/peter/rh-lean-worktree /home/peter/rh-cert /home/peter/cwr-audit /home/peter/membership-2581-verify /home/peter/rh_old_20261002; do
  F1="$W/ConnesWeilRH/Dev/C1RouteABinary64Bridge2674.lean"
  F2="$W/ConnesWeilRH/Dev/C1RouteACellIntegralCharge2675.lean"
  O1="$W/.lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteABinary64Bridge2674.olean"
  O2="$W/.lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteACellIntegralCharge2675.olean"
  [ -f "$F1" ] && echo "$W HAS2674SRC" >> $OUT
  [ -f "$F2" ] && echo "$W HAS2675SRC" >> $OUT
  [ -f "$O1" ] && echo "$W HAS2674OLEAN $(stat -c %y $O1 | cut -d. -f1)" >> $OUT
  [ -f "$O2" ] && echo "$W HAS2675OLEAN $(stat -c %y $O2 | cut -d. -f1)" >> $OUT
done
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676e.txt
