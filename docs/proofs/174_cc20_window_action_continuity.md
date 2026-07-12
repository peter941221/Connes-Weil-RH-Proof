# Proof 174: continuity of the finite-window log action

## Result

Accepted analytic infrastructure, but not an RH proof.

For every `lambda > 1` and continuous input `u`, the map

```text
t |-> ∫ s in [-log lambda, log lambda],
       K(t,s) * u(s) ds
```

is a continuous function of `t`.  Lean packages it as
`cc20GlobalLogWindowRegularActionContinuous` and exposes its pointwise
identification with `cc20GlobalLogWindowRegularAction`.

The proof uses Mathlib's parametric interval-integral continuity theorem and
the already-proved joint continuity of the global log kernel.  It does not
assume global boundedness or whole-line integrability of the oscillatory
profile.

## Verification

The aggregate WSL2 build and import-facing audit pass with only
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorryAx`, RH premise, or
stored continuity conclusion is present.

## Boundary

This only gives continuity of the finite-window output.  The next step is a
finite-window `MemLp` construction followed by indicator extension to the
common global carrier.  A global bounded operator, Fourier multiplier bound,
diagonal `-2 Dirac_0` split, same-test trace read-off, and RH are still open.
