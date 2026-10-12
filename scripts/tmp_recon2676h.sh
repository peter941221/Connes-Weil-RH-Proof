OUT=/tmp/recon2676h.txt
: > $OUT
for W in /home/peter/verify-2628-current /home/peter/cwrh-native /home/peter/rh /home/peter/membership-2581-verify; do
  echo "== $W" >> $OUT
  md5sum $W/ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean >> $OUT 2>&1
  ls $W/ConnesWeilRH/Dev/ | grep -E "267[0-6]" >> $OUT 2>&1
  ls -t $W/.lake/build/lib/lean/ConnesWeilRH/Dev/*.olean 2>/dev/null | head -3 | while read o; do echo "  OLEAN $(basename $o) $(stat -c %y $o | cut -d. -f1)" >> $OUT; done
done
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676h.txt
