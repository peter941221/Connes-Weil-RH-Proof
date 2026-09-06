# Record 1150 — P2 bilateral observable profile

Date: 2026-09-06

## Result

`C1P2BilateralProfile.lean` formalizes the exact profile seen by the
same-owner Weil functional:

```text
bilateralProfile F y = F.test y + F.test (-y).
```

The finite-prime sum depends on this profile only at the finitely many
visible points `y = log n`.  The archimedean numerator depends on the same
profile at every `y`, together with the separate origin value `F.test 0`.
Consequently, equality of the full profile plus equality at zero implies
equality of the archimedean term.  Combined with the prime-pair matching
theorem, the corresponding triple-vanishing defect gate is exactly zero.

The producer-facing refinement is explicit: a profile match restricted to the
image of the union of visible prime-power indices already suffices for
finite-prime cancellation, while the archimedean numerator difference is the
weighted profile difference minus the origin difference.  This is the exact
residual expression to which a later endpoint or low-rank envelope may be
applied.

The Lean declarations and paired audit build use only
`[propext, Classical.choice, Quot.sound]`; the focused build completed
successfully in 3660 jobs with no `error:` lines and no `sorryAx`.

## Route meaning

This is a FORMAL observable-interface reduction, not a positivity theorem.
It closes a bookkeeping ambiguity in Line C: the correction need only match
bilateral square-point sums for finite-prime cancellation, while any
archimedean comparison must control the same profile globally (and the value
at zero).  A hypothetical producer that matched the complete profile would
therefore cancel the whole defect gate rather than establish a negative
margin; the live target remains a finite-sample/low-rank residual estimate on
the healthy `CompactLog` owner.

## Guard

No route selection changes.  P2/C3 remains OPEN, and no RH or `qw >= 0`
statement is introduced.
