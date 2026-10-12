OUT=/tmp/probe2676f.txt
: > $OUT
M=/home/peter/rh/.lake/packages/mathlib
grep -rn "ofReal_cos\|cos_ofReal\|ofReal_sin\|sin_ofReal" $M/Mathlib/Data/Complex/Trigonometric.lean 2>/dev/null | head -6 >> $OUT
echo == >> $OUT
grep -rn "Real.cos_eq_re_exp\|cos_eq_re_exp\|re_exp_ofReal\|exp_ofReal_mul_I" $M/Mathlib --include=*.lean 2>/dev/null | head -6 >> $OUT
echo "== how does Real.cos relate: def search" >> $OUT
grep -rn "Real.cos x = Complex.cos\|Real.sin x = Complex.sin\|↑(Real.cos" $M/Mathlib/Data/Complex/Trigonometric.lean 2>/dev/null | head -4 >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_probe2676f.txt
