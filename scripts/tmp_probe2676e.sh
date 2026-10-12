OUT=/tmp/probe2676e.txt
: > $OUT
M=/home/peter/rh/.lake/packages/mathlib
echo "== exp_mul_I statement" >> $OUT
grep -rn "theorem exp_mul_I\|theorem cos_add_sin_mul_I" $M/Mathlib/Analysis/SpecialFunctions/Trigonometric/*.lean $M/Mathlib/Data/Complex/*.lean $M/Mathlib/Analysis/Complex/*.lean 2>/dev/null | head -5 >> $OUT
echo "== Complex.exp_bound re-projection usability: re_exp" >> $OUT
grep -rn "theorem re_exp\|Real.cos_eq_exp_real_mul_I\|exp_ofReal_mul_I" $M/Mathlib/Data/Complex/ExpBasic.lean $M/Mathlib/Data/Complex/Basic.lean 2>/dev/null | head -5 >> $OUT
grep -rn "theorem cos_eq\b\|cos_eq :" $M/Mathlib/Data/Complex/Trigonometric.lean 2>/dev/null | head -3 >> $OUT
echo "== Real cos defined via Complex" >> $OUT
grep -rn "def cos\b" $M/Mathlib/Data/Real/Basic.lean $M/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean 2>/dev/null | head -3 >> $OUT
cp $OUT /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/tmp_probe2676e.txt
