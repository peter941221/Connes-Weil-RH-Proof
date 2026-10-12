OUT=/tmp/recon2676i.txt
: > $OUT
find /home/peter -maxdepth 3 -name "*.log" -newermt "2026-10-10" 2>/dev/null | head -40 >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676i.txt
