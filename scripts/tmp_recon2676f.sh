OUT=/tmp/recon2676f.txt
: > $OUT
find /home/peter -maxdepth 6 -name "C1RouteABinary64Bridge2674.lean" -not -path "*/\.*" 2>/dev/null >> $OUT
find /home/peter -maxdepth 6 -name "C1RouteACellIntegralCharge2675.lean" -not -path "*/\.*" 2>/dev/null >> $OUT
find /home/peter -maxdepth 7 -name "C1RouteABinary64Bridge2674.olean" 2>/dev/null >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676f.txt
