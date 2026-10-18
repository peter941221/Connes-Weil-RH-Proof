# 2853 Route B sharper exponential probe

An attempted direct `Real.exp_bound` proof for the sharper interval
`exp(-8/3) > 1/16` and `exp(-13/5) < 1/8` did not close at Taylor order 10.
The resulting remainder bound is too loose for the desired rational margins.

This is a probe limitation, not a mathematical no-go. A higher Taylor order,
a better rational phase enclosure, or an existing exponential certificate is
needed before replacing the proved `[1/32,1/4]` box.
