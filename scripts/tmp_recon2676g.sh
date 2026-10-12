OUT=/tmp/recon2676g.txt
: > $OUT
for W in /home/peter/verify-2628-current /home/peter/cwr-current-20261002 /home/peter/verify-2617-controlled /home/peter/cwrh-native /home/peter/rh-lean-worktree /home/peter/rh-cert /home/peter/cwr-audit /home/peter/rh /home/peter/verify-2622 /home/peter/verify-2617 /home/peter/membership-2581-verify; do
  N=$(find $W -maxdepth 4 -name "C1RouteAIntervalAlgebra.lean" 2>/dev/null | head -1)
  [ -n "$N" ] && echo "$W :: $N" >> $OUT
  B=$(ls -t $W/build-logs 2>/dev/null | head -1)
  [ -n "$B" ] && echo "$W :: NEWLOG $B" >> $OUT
done
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676g.txt
