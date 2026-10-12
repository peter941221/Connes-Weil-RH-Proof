cd /home/peter/rh
ML=.lake/packages/mathlib
echo "== exp_bound surface =="
grep -rn "theorem exp_bound\|theorem Real.exp_bound" $ML/Mathlib/Analysis/ 2>/dev/null | head -8
echo "== complex abs_re lemmas =="
grep -rn "abs_re_le_norm\|theorem abs_re_le" $ML/Mathlib/Analysis/Complex/Exponentiation/ 2>/dev/null | head -5
grep -rn "abs_re_le_norm" $ML/Mathlib/Analysis/Complex/*.lean 2>/dev/null | head -5
echo "== exp_nat_mul =="
grep -rn "theorem Real.exp_nat_mul\|exp_nat_mul" $ML/Mathlib/Analysis/SpecialFunctions/Exp.lean 2>/dev/null | head -4
echo "== exp_bound proof context =="
sed -n '520,545p' $ML/Mathlib/Analysis/Complex/Exponential.lean
