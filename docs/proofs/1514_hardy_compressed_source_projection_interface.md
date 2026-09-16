# 1514 - Hardy-compressed root exact source-projection interface

## Status

Formal Lean interface; the S3 estimate remains open.

## Result

The actual Hardy-compressed root column has the exact identity

`E Q E C J = P C J + R C J`,

where `E` is the radial support projection, `Q` the Hardy/Fourier support
projection, `P` the source Sonin projection, `R` the prolate remainder, `C` the
selected root convolution, and `J` the source inclusion. Since the prolate
factor gives a square-summable `R C J` column on every named source basis, the
Hardy-compressed square-sum is equivalent to the square-sum of the single
source-projection leg `P C J`.

The declarations are

* `hardyCompressedRootEnergy_eq_sourceProjection_add_prolateRemainder`;
* `hardyCompressedRootEnergy_squareSum_iff_sourceProjectionRootEnergy`.

Both are in `ConnesWeilRH/Dev/C1G8R3GateAmbientNormalForm.lean`, with focused
axiom readback in its paired `...Audit` module. The proof uses the existing
all-scale prolate-factor square-sum and bounded pre/post-composition transfer.

This does not identify `P C J` with the already controlled complementary band
leg `B C J`; those are different operators. No S3 estimate, trace readback,
P2 sign, or RH conclusion follows.

## Acceptance

Build log: `/home/peter/rh/build-logs/1637_gate_projection_audit.log`.

The focused audit build completed successfully (3956 jobs), with no `error:` or
`sorryAx`; both new declarations print only
`[propext, Classical.choice, Quot.sound]`.
