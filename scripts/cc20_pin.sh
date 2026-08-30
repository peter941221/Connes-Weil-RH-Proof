#!/bin/bash
# Map CC20 rendered equation numbers and dump the displays relevant to the
# alpha / gamma / delta payloads into a UTF-8 file readable from Windows.
F=/home/peter/cc20/x/weil-compo.tex
O=/mnt/c/Projects/Connes-Weil-RH-Proof/tmp_cc20_pin.txt
{
  echo "=== numbered equation starts (last 45) ==="
  grep -n '\\begin{equation}' "$F" | tail -45
  echo
  echo "=== lines 1545-1565: the 0.00122 L1 estimate (alpha Fact-1) ==="
  sed -n '1545,1565p' "$F"
  echo
  echo "=== lines 1940-2010: W-infinity comparison + triple-vanishing kill ==="
  sed -n '1940,2010p' "$F"
  echo
  echo "=== eq 115/119 candidates: coercivity and (119) sums ==="
  grep -n 'computerverif\|spectral0\|approachk\|mainthmintro\|label{' "$F" | sed -n '1,60p'
} | iconv -f latin1 -t utf8 -c > "$O" 2>/dev/null
wc -c "$O"
