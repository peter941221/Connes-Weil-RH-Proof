# 1512 — Hilbert--Schmidt obstruction from the separated leakage orbit

Date: 2026-09-17.

**Status:** formal, compiled in `C1G8R3HilbertSchmidtOrthonormalObstruction.lean`
with paired audit leaf. This record is a no-go clarification for the
healthy-`CompactLog` B5 route; it is not an S3 closure.

The generic theorem
`ConnesWeilRH.Dev.summable_normSq_of_orthonormal` transports a squared-output
summability certificate from one Hilbert basis to every orthonormal sequence.
The proof extends the sequence's range to a Hilbert basis and uses the two
adjoint square-sum transports already present in `PositiveTrace`.

Applying it to the normalized separated translation orbit gives, for every
Hilbert basis of `finiteSCarrier`,

```text
not Summable (fun i =>
  || sourceRootCompletedRightCommutatorLeftLeg owner unitSoninScale (basis i) ||^2)
```

whenever the selected source Laplace value is nonzero. The contradiction is
exact: the orbit is orthonormal, its leakage column equals the actual operator
output, and the previously proved uniform lower bound makes the resulting
series nonsummable.

This rules out using the unprojected ambient leakage operator as a
Hilbert--Schmidt factor in the G8 energy proof. It does not address the live
S3 target, which is the source-compressed gate (equivalently the ambient
`P C P` square-sum); the Sonin projection can destroy the separated-orbit
obstruction, so no implication between the two estimates is asserted.

**Acceptance:** build log `1597_hs_obstruction_build.log` for the main leaf and
`1598_hs_obstruction_audit.log` for the audit leaf. Both have a successful
footer, zero `error:` lines, zero `sorryAx`, and the audit prints only
`[propext, Classical.choice, Quot.sound]`.

## Second obstruction: the full ambient band-root

The same argument also proves
`sourceRootCompletedBandRoot_not_hilbertSchmidt`: for every Hilbert basis of
`finiteSCarrier`, the squared columns of
`rootConvolution owner ∘L sourceBandProjection unitSoninScale` are not
summable under the same nonzero-Laplace hypothesis.

Here the exact decomposition is the committed identity
`sourceRootCompletedRangeLeftLeg + sourceRootCompletedRightCommutatorLeftLeg
= rootConvolution owner ∘L sourceBandProjection`. The range leg is already
Hilbert--Schmidt, hence tends to zero on the separated orbit. The leakage leg
has the established eventual lower bound, so the band-root output retains a
positive eventual lower bound. This rules out replacing the source-compressed
`P C P` target by the full ambient band-root. The source projection remains an
essential part of the live S3 problem.
