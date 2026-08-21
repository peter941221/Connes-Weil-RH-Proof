#!/usr/bin/env bash
D=/home/peter/projects/Connes-Weil-RH-Proof
echo "=== build/lib top ==="
ls "$D/.lake/build/lib/lean" 2>/dev/null | head
echo "=== ConnesWeilRH olean count (this package) ==="
find "$D/.lake/build/lib/lean/ConnesWeilRH" -name '*.olean' 2>/dev/null | wc -l
echo "=== mathlib present as dep? ==="
ls -d "$D/.lake/packages/mathlib" 2>/dev/null && echo "mathlib pkg dir: YES" || echo "mathlib pkg dir: NO"
find "$D/.lake" -path '*mathlib*' -name '*.olean' 2>/dev/null | wc -l | sed 's/^/mathlib olean count: /'
echo "=== my 5 deps built? ==="
for m in PositiveTrace GlobalConvolutionCrossing GlobalLogConvolution CompactLogConvolution C1SameOwnerWeil; do
  f=$(find "$D/.lake/build/lib/lean/ConnesWeilRH" -name "${m}.olean" 2>/dev/null | head -1)
  [ -n "$f" ] && echo "  $m: BUILT" || echo "  $m: MISSING"
done
echo "=== git state of this copy (is it a repo?) ==="
git -C "$D" log --oneline -3 2>/dev/null || echo "(not a git repo)"
