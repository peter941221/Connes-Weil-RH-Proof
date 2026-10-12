OUT=/tmp/recon2676l.txt
: > $OUT
for M in C1RouteAEndpointStrip C1RouteAStripTransfer C1RouteAOwnerTest C1RouteAExternalOwnerIdentity C1RouteAExternalOwnerDerivatives C1RouteAExternalOwnerZeroExtension C1RouteAOwnerScaleAudit C1RouteACorrectionCaptureParameters2584 C1RouteAIntervalAlgebra; do
  WMD5=$(md5sum /mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/$M.lean 2>/dev/null | cut -d" " -f1)
  LMD5=$(md5sum /home/peter/rh/ConnesWeilRH/Dev/$M.lean 2>/dev/null | cut -d" " -f1)
  if [ "$WMD5" = "$LMD5" ]; then echo "SAME $M" >> $OUT; else echo "DIFF $M win=$WMD5 wsl=$LMD5" >> $OUT; fi
done
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676l.txt
