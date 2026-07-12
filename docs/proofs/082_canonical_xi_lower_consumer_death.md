# 082 Canonical Xi Quotient Lower-Consumer Death Verdict

Date: 2026-07-12

## Result (superseded)

The standalone-consumer verdict below is superseded by proof 083. Plan 025 is
not rejected outright; only the claim that the quotient has no lower consumer
is rejected.
The Xi quotient can at most establish the converse Weil implication:

```text
off-critical zero -> compact triple-vanishing test with QW < 0.
```

The active Lean route needs the opposite sign for every admissible test. That
sign is not supplied by the quotient and is not a consequence of existing
source data.

## Direct code evidence

`ConnesWeilRH/Route/Exhaustion.lean` defines `FullWeilPositivity` with the
field `fixedSPositiveTraceReadOff : FixedSPositiveTraceReadOff inputs g`.
Its constructor `full_weil_positivity_of_source_backed_fixed_s` requires that
field. The CC20 exit in `ConnesWeilRH/Source/CC20.lean` consumes an explicit
premise `hpositive : input.fullWeilPositivity`; it does not prove it.

The Xi detector supplies neither `FixedSPositiveTraceReadOff` nor a replacement
theorem proving nonnegativity of the full Weil form. Its negative test therefore
has no route consumer that yields a contradiction.

## Why the M4 detour does not repair this

The M4/CC20 remainder is `-2 Id + K_I` with `K_I` compact. Compactness only
gives a finite-dimensional control space via
`CompactBadSpace.exists_finiteDimensional_controlSpace`; it does not give a
positive-trace read-off or a norm bound making the form nonnegative on the
detector. Proof 080's translation argument gives algebraic separation before
cutoff, but cannot manufacture the missing sign premise after cutoff.

Thus the quotient alone proves only the classical converse Weil criterion. It
may nevertheless lower the active root when combined with fixed-interval M4
bad-space orthogonalization, as recorded in proof 083.

## Decision

```text
X1 orbit quotient: survives conceptually
X2 inverse tail: analytic work remains
X3 compact cutoff: analytic work remains
X4 orbit sign: survives algebraically
X5 lower consumer: standalone version rejected; compact bad-space rescue open
X6 Lean owner: forbidden until proof 083 gates pass
```

The compact bad-space rescue is the permitted reopening mechanism; more tail
estimates alone are insufficient.
