# 2890 Route B D4 Cauchy remainder assembly

Using the conservative rational circle bound `M = 13.77903608911726`, radius
`R = 0.05`, target radius `r = 0.01`, and order-22 tail, the geometric Cauchy
remainder formula gives

`M * (r/R)^22 / (1-r/R) = 7.2242e-15`.

The order-20 truncated positivity lower bound is `37.154...`, so this assembled
tail is about `1.94e-16` of that margin. The arithmetic assembly is exact over
rationals, but the formal analytic theorem and the provenance link from the
interval artifact to `M` remain open.
