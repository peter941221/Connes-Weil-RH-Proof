# 1731 — Critical Mellin profile second-derivative integrability

## Result

`integrable_ccm24CriticalMellinLogProfileSecondDerivFormula` proves that the
explicit second-derivative formula for the critical Mellin log profile is
absolutely integrable for every Schwartz input. The positive logarithmic tail
uses the zeroth Schwartz seminorm; the negative tail uses the third seminorm.
The other two terms reuse the committed first-profile and chain-term
integrability theorems.

## Route meaning

This is the concrete Sobolev input for the quadratic Fourier-tail consumer on
the Schwartz core. It does not identify the arbitrary source-carrier Hardy
output with this profile, does not prove a uniform kernel-diagonal bound, and
does not close S3 or RH. The remaining interface is the Hardy-output and
source-carrier regularity transfer.

## Acceptance

The paired Audit leaf prints the chain-rule and integrability declarations.
The focused build completed successfully (2967 jobs), with zero `error:` and
zero `sorryAx`; the declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.
