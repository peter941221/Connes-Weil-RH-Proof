#!/usr/bin/env bash
for D in /home/peter/cwr-stage3-20260819 /home/peter/projects/Connes-Weil-RH-Proof /home/peter/oss-targets/connes-weil-rh-proof; do
  echo "=== $D ==="
  [ -f "$D/lakefile.toml" ] && printf 'lakefile: YES\n' || printf 'lakefile: NO\n'
  if grep -q frontierHS_summable "$D/ConnesWeilRH/Dev/C1Stage3FrontierHS.lean" 2>/dev/null; then printf 'FrontierHS-summable: YES\n'; else printf 'FrontierHS-summable: no\n'; fi
  [ -f "$D/ConnesWeilRH/Dev/C1Stage3FrontierCrux.lean" ] && printf 'Crux: present\n' || printf 'Crux: absent\n'
  printf 'olean-count: %s\n' "$(find "$D/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l)"
done
