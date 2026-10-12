OUT=/tmp/recon2676k.txt
: > $OUT
for W in /home/peter/rh /home/peter/verify-2628-current /home/peter/cwrh-native; do
  echo "== $W  total=$(ls $W/.lake/build/lib/lean/ConnesWeilRH/Dev/*.olean 2>/dev/null | wc -l)" >> $OUT
  for M in C1RouteAEndpointStrip C1RouteAStripTransfer C1RouteAOwnerTest C1RouteAExternalOwnerIdentity C1RouteAExternalOwnerDerivatives C1RouteAExternalOwnerZeroExtension C1RouteAOwnerScaleAudit C1RouteACorrectionCaptureParameters2584 C1RouteAIntervalAlgebra C1RouteABinary64Bridge2674; do
    [ -f "$W/.lake/build/lib/lean/ConnesWeilRH/Dev/$M.olean" ] && echo "  OK $M" >> $OUT
  done
done
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_recon2676k.txt
