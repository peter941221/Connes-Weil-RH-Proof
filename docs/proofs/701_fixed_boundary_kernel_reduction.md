# Proof 701: Fixed Boundary-Kernel Reduction

## What is established

For the translated compact root pair, the two zero-leg hypotheses are read
back through the bounded sandwich onto the same translated vector:

```text
hleft  -> negativeBoundaryRootFactor (U_(log lambda) x) = 0
hright -> positiveBoundaryRootFactor (U_(log lambda) x) = 0
```

Here `U_t` is the genuine logarithmic translation on `finiteSCarrier`.  The
negative leg uses the adjoint identity for the inverse translation, so both
boundary factors are evaluated at exactly `U_(log lambda) x`.

The existing half-line factor identities then give zero for the full boundary
factor on each projection.  Since the negative and positive half-line
projections add to the identity, Lean proves

```text
translatedBoundaryPair_zero_imp_fullBoundaryRootFactor_zero

translated left = 0 and translated right = 0
  -> fullBoundaryRootFactor (U_(log lambda) x) = 0
```

The proof is an exact algebraic reduction: it uses the translation adjoint
law, `boundedSandwich` readback, the two projection factor identities, and the
negative/positive projection split.

## Why this matters

Proof 700 reduces dense range of `fixedPhysicalSourceInput` to joint
injectivity of the two translated boundary legs.  Proof 701 reduces the
resulting common kernel further to the kernel of the single full boundary
factor on the translated Sonin carrier.  This identifies the remaining
analytic producer without changing its domain or assuming Fourier
multiplier injectivity.

The conclusion is only a zero implication at a translated vector.  It does
not prove injectivity, dense range, Gate 3U, the finite-S sign, Burnol's
identity, or unconditional `_root_.RiemannHypothesis`.

## Verification

The focused source and audit passed in Ubuntu-24.04 WSL2 with `3286` jobs.
The shared `CCM25Concrete` aggregate passed with `3974` jobs, and the full
default build passed with `4055` jobs.  The audit reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom was added.
