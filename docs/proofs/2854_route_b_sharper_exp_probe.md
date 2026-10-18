# 2854 Route B sharper exponential probe

The attempted order-30 proof exposed an interface constraint in Mathlib:
`Real.exp_bound` requires `|x| <= 1`. Direct calls at `-8/3` and `-13/5`
therefore do not satisfy the theorem's premise.

The next valid construction must split the exponent into pieces in `[-1,1]`
and combine them with `Real.exp_add`. This is a proof-interface issue, not a
mathematical no-go.
