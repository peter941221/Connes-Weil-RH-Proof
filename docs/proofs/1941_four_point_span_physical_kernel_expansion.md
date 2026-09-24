# Record 1941: four-point span physical-kernel expansion

## Result

The existing pair-basis span expansion has been extended with an explicit
physical form. For any finite real span `spanObj w y` and any prime-power
index `n`, its signed profile term is exactly the real part of the finite
double sum whose `(i,j)` entry is

```text
integral star((w i).test(-t)) * (w j).test(log n - t)
  + integral star((w i).test(-t)) * (w j).test(-log n - t).
```

The formal declarations are
`bilateralProfile_pairTest_eq_physical_integral_sum` and
`signedProfileTerm_spanObj_eq_pair_physical_integral_quadratic` in
`C1P2SpanProfileMatrix.lean`.

## Route significance

This closes the owner mismatch identified in record 1940 at the algebraic
readback level: the formula applies directly to
`h(lambda) = u - lambda * g`, not only to an original `OrbitG8Geometry`
owner. The already-formal four-pair quadratic and high-shell transport can
therefore consume the same physical pair entries.

No sign estimate is hidden in this expansion. The remaining core obligation
is the strict signed budget for these four pair channels at the gate-selected
coefficient.

## Verification

Focused WSL build `20260924_span_physical4.log` completed successfully with
3789 jobs. The paired audit reports only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` occurs.
