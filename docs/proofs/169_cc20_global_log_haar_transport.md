# Proof 169: common log-Haar carrier and exact finite-window transport

## Result

Good route-level infrastructure, but not an RH proof.

All finite multiplicative windows now have a common ambient Hilbert space in
the logarithmic coordinate. The source Haar integral on
`[1/lambda, lambda]` is formally equal to the Lebesgue integral on
`[-log lambda, log lambda]` after `rho = exp t`.

## What is proved

`GlobalLogHaar.lean` defines

```text
cc20GlobalLogL2 = Lp C 2 volume
cc20LogWindow lambda = [-log lambda, log lambda]
cc20LogWindowProjection lambda : cc20GlobalLogL2 -> cc20GlobalLogL2
```

The projection is multiplication by the `L-infinity` indicator of the log
window. Lean proves its almost-everywhere representative formula and
idempotence. Every `PositiveIntervalCompactTest` is also pulled back by
`t |-> test(exp t)` to an element of the same global `L2` carrier, with compact
support inherited from the positive multiplicative support.

`HaarLogTransport.lean` proves, for every continuous `f : R -> C`,

```text
integral_[1/lambda,lambda] f(rho) d rho/rho
  = integral_[-log lambda,log lambda] f(exp t) dt.
```

The proof expands the weighted subtype measure, applies
`integral_subtype_comap`, uses the interval-integral substitution theorem for
`Real.exp`, and discharges the endpoint identities explicitly.

## Why it matters

The previous parameterized operators lived on a different subtype `L2` space
for each `lambda`. That is enough for per-window compactness but not for a
common bad space, strong convergence, or exhaustion. The new carrier removes
that type-level mismatch without asserting an unproved zero-extension
isometry.

## Verification

The retained WSL2 Lake cache passed:

```text
lake build ConnesWeilRH.Source.CC20Concrete.HaarLogTransport
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

Focused axioms for the projection formula, idempotence, pullback `L2`
membership, representative formula, and Haar-log transport are exactly:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, RH premise, Weil-positivity premise, or stored transport
conclusion.

## Remaining bottom

This result does not yet transport the parameterized regular-kernel operator
itself onto the global carrier. The next obligation is the same-object kernel
action identity in log coordinates, followed by common-domain exhaustion,
uniform control of the three-point bad space, the diagonal
`-2 Dirac_0 -> -2 Id` form identity, and the CC20 same-test trace read-off.

RH remains unproved.
