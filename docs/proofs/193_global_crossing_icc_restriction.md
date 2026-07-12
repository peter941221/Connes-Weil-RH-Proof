# Global crossing `Icc` restriction

## Result

Good: the whole-line operator `cc20SingleCrossingOperator b` now has an
explicit almost-everywhere function formula. For `b >= 0`, its nonzero
crossing region is exactly the interval `Icc (-b) 0`, up to the null endpoint
at zero.

## Formula

The Lean theorem
`cc20SingleCrossingOperator_coeFn` first gives

```text
J_b u(t)
  = 1_[t < 0] 1_[t+b >= 0] u(t+b)
```

almost everywhere. The strengthened theorem
`cc20SingleCrossingOperator_coeFn_eq_Icc_indicator` gives, when `0 <= b`,

```text
J_b u(t) = 1_[-b <= t <= 0] u(t+b)
```

almost everywhere. The endpoint `t=0` is removed using the atomless Lebesgue
measure fact `volume.ae_ne 0`.

## Why this matters

The compact crossing owner uses a source coordinate `s in [0,b]`. The global
operator sends it to the output coordinate `t=s-b in [-b,0]`. Thus the
compact source interval is not an arbitrary truncation: it is the exact
boundary interval selected by the global half-line projections.

This closes the geometric restriction obligation. It does not yet prove the
smoothed identity

```text
compact A†B factorization = C_h* C_h J_b
```

on the whole-line `L2` carrier. That identity still requires a bounded
convolution operator and an extension/restriction argument for the same
compact test.

## Verification

Focused import audit:
`ConnesWeilRH/Dev/SelectedCrossingKernelAudit.lean`.

Both crossing declarations use only:

```text
propext
Classical.choice
Quot.sound
```

The WSL build of `ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing` passes.
