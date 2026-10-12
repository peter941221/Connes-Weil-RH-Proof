for W in /home/peter/rh /home/peter/projects/Connes-Weil-RH-Proof; do
  if [ -d "$W/.lake/build/lib/lean" ]; then
    echo "WORKSPACE $W"
    ls "$W"/ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean "$W"/ConnesWeilRH/Dev/C1RouteACellIntegralCharge2675.lean 2>/dev/null | sed 's/^/  HAVE /'
    ls "$W"/_*.log 2>/dev/null | tail -2 | sed 's/^/  LOG /'
    M="$W/.lake/packages/mathlib"
    ls "$M/Mathlib/Analysis/Calculus/MeanValue.lean" 2>/dev/null | sed 's/^/  MV /'
  fi
done
