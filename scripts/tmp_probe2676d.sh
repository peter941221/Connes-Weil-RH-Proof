OUT=/tmp/probe2676d.txt
: > $OUT
M=/home/peter/rh/.lake/packages/mathlib
echo "== MeanValue 727 context" >> $OUT
sed -n '700,740p' $M/Mathlib/Analysis/Calculus/MeanValue.lean >> $OUT
echo "== exp_mul_I def" >> $OUT
grep -rn "exp_mul_I" $M/Mathlib --include=*.lean | head -4 >> $OUT
echo "== Real.exp_le_exp" >> $OUT
grep -rn "theorem exp_le_exp\b\|exp_le_exp " $M/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean $M/Mathlib/Order/Interval/*.lean 2>/dev/null | head -3 >> $OUT
grep -rn "theorem exp_le_exp\b" $M/Mathlib --include=*.lean | head -3 >> $OUT
echo "== exp monotone strict" >> $OUT
grep -rn "theorem exp_strictMono\|theorem exp_le_exp_iff" $M/Mathlib --include=*.lean | head -3 >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_probe2676d.txt
