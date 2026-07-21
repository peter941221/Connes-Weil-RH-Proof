# Proof 473: Detector signed kernel response

## Result

Proof 472 exposed four inner products of the same negative and positive
compact-root kernel legs.  Proof 473 recombines them before any estimate.

Let

```text
J = P^dagger N - N^dagger P,
```

where `N` and `P` are the unshifted negative and positive compact-window
kernel factors.  If `T` is translation by `log(lambda)` and `L=E Q`, Lean
proves

```text
primitiveOuterReflected(x,y)
  = <T L^dagger x, J T y> + <T x, J T L^dagger y>.
```

Thus the four terms are one two-sided signed response, not four independent
quantities.  Moreover `J` is exactly the existing `signedBoundaryOperator`,
and hence exactly

```text
[positive-half-line projection, windowed boundary detector].
```

The same owner supplies both `IsTraceClassAlong` on the named global basis and
the exact skew-adjoint identity `J^dagger = -J`.

The bases used by the compact pair certify trace legality but do not change
`J`.  The complete displacement atom remains one global-basis `tsum` of this
signed response plus the still-coupled second-support/prolate remainder.

## Boundary

This is an algebraic cancellation and owner identification.  It does not yet
bound the signed scalar uniformly in the finite Euler set.  Do not estimate
the two displayed inner products separately: compact support must be applied
to their sum together with the coupled second-support/prolate response.

The compact-support cancellation, coupled remainder kernel control, renewal
trace exchange, uniform Gate 3U bound, finite-S sign, Burnol identity, and
`_root_.RiemannHypothesis` remain open.
