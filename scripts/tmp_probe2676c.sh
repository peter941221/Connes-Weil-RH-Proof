OUT=/tmp/probe2676c.txt
: > $OUT
M=/home/peter/rh/.lake/packages/mathlib
echo "== Real exp_bound / exp_bound' statements" >> $OUT
sed -n '524,545p' $M/Mathlib/Analysis/Complex/Exponential.lean >> $OUT
echo "== MeanValue norm_image_sub signature" >> $OUT
grep -n "norm_image_sub_le_of_norm_deriv_le" $M/Mathlib/Analysis/Calculus/MeanValue.lean >> $OUT
echo "== exp cos sin identity" >> $OUT
grep -rn "exp (x \* I)\|exp_ofReal_mul_I\|exp (↑x \* I)\|cos_add_sin\|exp_mul_cos\|Real.cos_exp\|Complex.exp_eq" $M/Mathlib/Data/Complex/ExpBasic.lean 2>/dev/null | head -6 >> $OUT
grep -rln "exp (x \* I)" $M/Mathlib/Data/Complex $M/Mathlib/Analysis/SpecialFunctions 2>/dev/null | head -5 >> $OUT
grep -rn "theorem exp_mul_I\|theorem exp_eq_exp_Im\|theorem exp_re\b" $M/Mathlib/Data/Complex/Exp.lean $M/Mathlib/Data/Complex/ExpBasic.lean 2>/dev/null | head -5 >> $OUT
echo "== sin/cos bounds lemmas" >> $OUT
grep -rn "theorem sin_lt\|theorem cos_lt\|sin_le_sin\|theorem cos_pos" $M/Mathlib/Analysis/SpecialFunctions/Trigonometric/Angle.lean $M/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean 2>/dev/null | head -5 >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_probe2676c.txt
