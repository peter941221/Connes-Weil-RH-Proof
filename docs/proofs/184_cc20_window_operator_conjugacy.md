# Proof 184: Fixed-window Haar/log operator conjugacy

## Result

`GlobalLogKernel.lean` now packages the two carrier transports into
`cc20WindowHaarRestrictedLogL2IsometryEquiv`:

```text
Lp Complex 2 (cc20WindowHaarMeasure lambda hlambda)
  ≃ₗᵢ[Complex]
Lp Complex 2 (volume.restrict (cc20LogWindow lambda))
```

The module proves the exact continuous-core identity
`cc20WindowHaarRestrictedLogL2IsometryEquiv_apply_logRestriction`.
It also defines the restricted-window endomorphism
`cc20GlobalLogWindowRestrictedL2Endomorphism` and the transported Haar
operator `cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator`.

The regular-kernel action and the restricted global-log action agree on the
bounded-continuous core. `BoundedContinuousFunction.toLp_denseRange` then
extends this equality to the complete restricted `L2` space, proving:

```text
cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda
  = cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator lambda hlambda
```

The proof uses the same finite-window object on both sides. The almost-
everywhere steps explicitly transport `toLp` representatives through `exp`,
the subtype inclusion, and the restriction map.

## Verification

Using the retained WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogKernel
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

The aggregate build completed `3504/3504` jobs. The import-facing audit for
the new declarations reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, project axiom, or unconditional RH premise appears.

## Boundary

This is a fixed-`lambda` regular-kernel conjugacy result. It does not prove
Hilbert--Schmidt positive-trace transport, a common-window limit, the
diagonal `-2 Id` distributional identity, the same-test CC20 trace read-off,
uniform three-point bad-space control, or unconditional RH.
