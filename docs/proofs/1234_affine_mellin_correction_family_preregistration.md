# 1234 - Affine finite-Mellin correction family

Date: 2026-09-09.

Status: LANDED focused formal source-family brick.  This record claims no P2
sign, no profile factorization, and no RH result.

Consumer: the same healthy-`CompactLog` selected-detector owner.  The brick
serves G4/G6 by replacing the arbitrary choice selector with an explicitly
linear coefficient-to-node map and a linear right inverse.

## Target

For positive coordinates `a = exp lower`, `b = exp upper`, define the linear
map

```text
E : (WindowedPositiveIntervalCompactTest a b →₀ ℂ)
      →ₗ[ℂ] (FiniteMellinNode nodes → ℂ)
```

by the finite Mellin vectors already used in the source interpolation proof.
Use `windowedFiniteMellinVector_span_top` to prove `E` is surjective and take
a linear right inverse `R`.  The resulting correction

```text
y ↦ compactLogTestOfWindow (combination (R y))
```

must carry the existing support bound and realize `y` at every node.  The
right-inverse identity is the only new algebraic content; it is not a sign
theorem and does not assert that the selected-owner physical profile factors
through `y`.

## Guards

Use the existing positive-window combination and compact-log conversion.  Do
not introduce a stored positivity field, `qw`, or an RH-equivalent premise.
The resulting family must be labeled as an affine/linear source family only;
the selected-owner map remains nonlinear after convolution-square formation.

## Falsifier

If the span-top theorem cannot be converted into a surjective linear map, or
if the right-inverse readback fails to transport through
`compactLogTestOfWindow`, stop without inventing a matrix inverse or a finite
dimensional numerical rank argument.

## Verification

Deliver an owning module and paired audit.  Acceptance requires the resource
runner success footer, zero `error:` and `sorryAx`, and standard three-axiom
audits only.

RH is not claimed.

## Post-run addendum (2026-09-09)

The owning module
`ConnesWeilRH/Dev/C1HealthyYoshidaAffineCorrection.lean` and paired audit
landed.  It defines `windowedMellinEvaluationMap`, proves surjectivity from
`windowedFiniteMellinVector_span_top`, chooses a linear right inverse, and
proves the compact-log correction's support and exact `laplaceAt` readback.
The selected-owner profile remains nonlinear after convolution-square
formation; no factorization or sign theorem was added.

Acceptance evidence: WSL resource-runner log
`/home/peter/rh/build-logs/1234_affine_correction_retry10.log`, success footer
`Build completed successfully (3662 jobs)`, zero `error:` and zero `sorryAx`;
the paired audit prints only `[propext, Classical.choice, Quot.sound]`.
