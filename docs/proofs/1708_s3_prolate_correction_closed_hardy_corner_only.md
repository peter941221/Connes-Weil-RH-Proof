# 1708 — S3 prolate correction closed; Hardy corner is the sole survivor

Date: 2026-09-20.

Status: FORMAL brick. RH is not claimed.

## Result

The direct source-compressed root is

```text
J† C J = J† (E Q E) C J - J† R C J,
```

where `J` is the committed source inclusion, `C` the selected root
convolution, `E` the radial projection, `Q` the Fourier-support projection,
and `R` the committed source-prolate remainder.

The new theorem
`sourceCompressedRoot_prolateTerm_sourceBasis_normSq_summable` proves, for
every named source Hilbert basis, that the correction `J† R C J` has summable
column norm squares.  The proof factors `R = K† K`, uses the already proved
all-scale square-summability of the prolate factor `K`, and applies bounded
pre- and post-composition in the Hilbert–Schmidt ideal.

The companion theorem
`sourceCompressedRoot_squareSum_iff_hardyCorner_squareSum` therefore proves
the exact iff: the S3 survivor square-sum is equivalent to the square-sum of
the Hardy corner `J† (E Q E) C J`.  No estimate on that corner is asserted.

## Consequence for the active route

This removes the prolate correction from the S3 producer obligation.  The
remaining analytic task is now one operator, the Hardy-corner kernel.  The
fixed-window no-go from record 1707 still applies: its ambient trace cannot
be bounded by plain compact-window Hilbert–Schmidt growth.  A producer must
use the coupled radial/Fourier carrier structure.

Evidence: focused build log `1708_prolate_term_energy_v7.log`, 3958 jobs,
zero `error:`, zero `sorryAx`; the paired Audit leaf prints only
`[propext, Classical.choice, Quot.sound]`.
