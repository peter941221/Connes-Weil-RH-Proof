OUT=/tmp/probe2676b.txt
: > $OUT
M=/home/peter/rh/.lake/packages/mathlib
echo "== exp_bound / exp_bound' anywhere" >> $OUT
grep -rn "theorem exp_bound" $M/Mathlib --include=*.lean | head -6 >> $OUT
echo "== add_one_le_exp anywhere" >> $OUT
grep -rn "add_one_le_exp" $M/Mathlib --include=*.lean | grep theorem | head -4 >> $OUT
echo "== exp_le_one anywhere" >> $OUT
grep -rn "theorem exp_le_one\|exp_le_one_iff" $M/Mathlib --include=*.lean | head -4 >> $OUT
echo "== exp_neg anywhere" >> $OUT
grep -rn "theorem exp_neg\b" $M/Mathlib --include=*.lean | head -3 >> $OUT
echo "== norm_image_sub_le_of_norm_deriv_le anywhere" >> $OUT
grep -rln "norm_image_sub_le_of_norm_deriv_le" $M/Mathlib --include=*.lean | head -4 >> $OUT
grep -rn "theorem norm_image_sub_le_of_norm_deriv_le\b\|norm_image_sub_le_of_norm_deriv_le " $M/Mathlib/Analysis/Convex/Taylor.lean 2>/dev/null | head -4 >> $OUT
echo "== exp_mul_I anywhere" >> $OUT
grep -rn "theorem exp_mul_I\|theorem exp_nat_mul_I\|cos_add_sin_mul_I\|exp_re_im" $M/Mathlib/Data/Complex/*.lean $M/Mathlib/Analysis/SpecialFunctions/*.lean 2>/dev/null | head -8 >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_probe2676b.txt
