# 1926 — Route A final-sign no-go for the current selector

Date: 2026-09-24.

Status: scoped no-go. This does not rule out a new variational or
sign-constrained selector, and RH is not claimed.

## Audited target

After the exact reduction in record 1925, Round 2 needs the strict inequality

```text
archimedeanTerm(selectedOwner.square)
  + integral(actual grouped finite aggregate)
  <= -epsilon,  epsilon > 0.
```

The visible-prime terms must remain grouped so their cancellation is preserved.

## Why the current selector cannot supply it

`SelectedPhysicalDerivativeCorrection` now stores a derivative seminorm and a
pointwise derivative bound. This removes the old missing-data error, but the
construction defines the cost from the selected Schwartz derivative itself;
it proves only that the cost is finite and nonnegative. It supplies no bound
of that cost in terms of the finite Mellin assignment, no phase constraint, no
variation bound for the aggregate, and no relation to the Archimedean term.

Independently, the existing formal theorem
`C1FiniteMellinPhysicalSeparation.exists_laplace_vanishing_test_value_one`
constructs a compact test supported in a controlled window that vanishes at
every prescribed finite Mellin node but has a prescribed nonzero physical
value. Thus finite interpolation data do not determine the physical profile.
Adding the automatically finite derivative seminorm does not remove this
freedom, because no uniform cost budget is proved for the zero-node
perturbation.

Therefore the final sign cannot be derived from the current selector fields
without introducing a genuinely new ingredient: a variational selector with a
proved cost bound, or a sign/phase theorem for the actual grouped physical
kernel. Adding another residual certificate would simply assume the target.

## Named result

```text
NO-GO-A2-FINAL-SIGN-CURRENT-SELECTOR
```

Scope: the current classical interpolation selector plus its derivative cost
does not close Round 2's final signed margin. This is not a mathematical
no-go for every possible selector. It is the stop result required by the
campaign rules; Route A must change the selector mechanism before Round 3.
