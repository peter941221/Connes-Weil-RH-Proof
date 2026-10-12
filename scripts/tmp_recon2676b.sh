for W in /home/peter/rh /home/peter/projects/Connes-Weil-RH-Proof; do
  echo "== $W"
  ls "$W/.lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteACellIntegralCharge2675.olean" 2>/dev/null | sed 's/^/  OLAN2675 /'
  ls "$W/.lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteABinary64Bridge2674.olean" 2>/dev/null | sed 's/^/  OLAN2674 /'
  ls -t "$W"/_*.log "$W"/build-logs/*.log 2>/dev/null | head -2 | sed 's/^/  NEWLOG /'
done
