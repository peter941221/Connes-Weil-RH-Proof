OUT=/tmp/recon2676.txt
: > $OUT
for W in /home/peter/rh /home/peter/projects/Connes-Weil-RH-Proof; do
  echo "== $W" >> $OUT
  ls "$W/.lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteACellIntegralCharge2675.olean" >> $OUT 2>&1
  ls "$W/.lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteABinary64Bridge2674.olean" >> $OUT 2>&1
  ls -t "$W"/_*.log >> $OUT 2>&1 | head -2
  ls -t "$W"/build-logs/*.log >> $OUT 2>&1 | head -2
done
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676.txt
