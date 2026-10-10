#!/bin/bash
# Record-2663 recon: mirror state, import/olean presence, Mathlib name probes.
# Run from Windows side via:  wsl.exe bash -lc 'tr -d "\r" < <this> | bash'
cd /home/peter/rh || { echo "MIRROR MISSING"; exit 1; }
M=/home/peter/rh/.lake/packages/mathlib/Mathlib
echo "=== mirror state ==="
git branch --show-current
git log --oneline -1
echo "=== source presence ==="
ls ConnesWeilRH/Dev/C1RouteAAnalyticMomentNormalization2618.lean \
   ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean \
   ConnesWeilRH/Dev/C1RouteAAdaptiveN05440Minus2542.lean 2>&1
echo "=== olean presence ==="
ls .lake/build/lib/lean/ConnesWeilRH/Dev/ 2>/dev/null | wc -l
ls .lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteAAnalyticMomentNormalization2618.olean \
   .lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.olean \
   .lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteAAdaptiveN05440Minus2542.olean 2>&1
echo "=== 2618 def shape ==="
grep -n "def normalizedMomentIntegrand2618" -A 3 ConnesWeilRH/Dev/C1RouteAAnalyticMomentNormalization2618.lean
echo "=== 2542 pair defs ==="
grep -n "RatPair2542\|def embedPair2542" ConnesWeilRH/Dev/C1RouteAAdaptiveN05440Minus2542.lean | head -8
echo "=== mathlib name probes ==="
grep -rn "theorem exp_one_gt_two" "$M" --include=*.lean | head -3
grep -rn "theorem norm_exp" "$M" --include=*.lean | head -3
grep -rn "theorem integral_comp_add_left" "$M" --include=*.lean | head -3
grep -rn "theorem uIoc_subset_uIcc" "$M" --include=*.lean | head -3
grep -rn "theorem sum_integral_adjacent_intervals_Ico" "$M" --include=*.lean | head -3
grep -rn "theorem intervalIntegrable_congr" "$M" --include=*.lean | head -3
grep -rn "theorem norm_le_abs_re_add_abs_im" "$M" --include=*.lean | head -3
grep -rn "theorem cast_add" "$M/Data/Rat" --include=*.lean | head -5
grep -rn "exp_nat_mul" "$M" --include=*.lean | head -3
echo "=== done ==="