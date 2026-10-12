OUT=/tmp/recon2676j.txt
: > $OUT
find /home/peter -maxdepth 3 -name "*.log" -newermt "2026-10-10" 2>/dev/null | while read f; do
  if grep -l "C1RouteAIntervalAlgebra\|C1RouteABinary64Bridge2674\|C1RouteACellIntegralCharge2675\|C1RouteABumpEnclosure" "$f" >/dev/null 2>&1; then
    echo "$f" >> $OUT
  fi
done
echo === >> $OUT
find /home/peter -maxdepth 3 -name "*.log" -newermt "2026-10-11 12:00" 2>/dev/null | tail -20 >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676j.txt
