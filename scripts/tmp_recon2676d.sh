OUT=/tmp/recon2676d.txt
: > $OUT
ls -d /home/peter/* 2>/dev/null >> $OUT
echo --- >> $OUT
find /home/peter -maxdepth 2 -name "lean-toolchain" 2>/dev/null | while read f; do echo "$f -> $(cat $f)" >> $OUT; done
echo --- >> $OUT
find /home/peter -maxdepth 3 -name "C1RouteABinary64Bridge2674.lean" 2>/dev/null >> $OUT
echo --- >> $OUT
find /home/peter -maxdepth 4 -name "2675*.log" -o -maxdepth 4 -name "*2675*build*.log" 2>/dev/null | head >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676d.txt
