# 1885 - Taper Gram gap upper bound

Date: 2026-09-23.

Status: Formally verified in Lean; supplies an upper ceiling for any tapered
Gram gap certificate.

For a node family containing a zero node, the unit coordinate vector at that
node has constant representer `1`.  If the taper is bounded above by one, its
quadratic energy is at most the interval length.  Therefore the theorem
`windowTaperGram_gap_le_interval_length_of_zero_node` proves

```text
alpha <= b - a
```

for every `alpha` satisfying the tapered Gram lower-bound hypothesis.

This is an upper bound, not a positive-gap supplier.  In particular, on the
route-alpha register the zero node is always present, so any proposed scalar
threshold must fit below this interval-length ceiling.  The theorem does not
yet prove impossibility of every taper consumer, and it supplies no
detector-specific semi-local positivity or RH conclusion.

Verification: WSL focused build `taper-gap-upper-1885c.log`; successful footer
for 3551 jobs, zero `error:` lines, zero `sorryAx`, and the paired Audit
declaration uses only `[propext, Classical.choice, Quot.sound]`.
