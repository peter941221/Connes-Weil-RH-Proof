# Record 2500 — price of the formal exponential split

Before propagating the 2498 split through the weighted curvature, the exact
rational split formula was compared with the directed-MPFR exponential on all
9,994 local owner/cell pairs.  Among the 9,796 pairs representable as nonzero
binary64 values, the median ratio was `1.0000000000000056` and the maximum
was `1.000000000000138` (cell 129, family 6, `n = 686`).  198 more extreme
values underflowed binary64 and are reported separately; this diagnostic does
not use their zero as a mathematical value.

The result supports continuing with the formal split: its observed finite
precision overhead is negligible relative to the 2496 payload scale.  The
minimum ratio is not used as a soundness check: the external wrapper converts
the exact rational endpoint computation to binary64, so this statistic can
under-read the true comparison.  The Lean theorem, not this ratio table, is
the soundness anchor.  This remains external pricing evidence, not a proof of
the per-cell inequality.  No producer GO or RH claim is made.
