# Proof 185: Restricted-window positive-trace transport

## Result

The fixed-window operator conjugacy from proof 184 now transports the
Hilbert--Schmidt layer to the restricted logarithmic carrier.

For any Hilbert basis of

```text
Lp Complex 2 (volume.restrict (cc20LogWindow lambda))
```

`cc20GlobalLogWindowRestrictedL2HaarPreimageBasis` constructs the Haar basis
obtained by composing its representation with the finite-window Haar/log
isometry. The declaration
`cc20GlobalLogWindowRestrictedL2Endomorphism_basis_normSq_summable` proves
summability of the restricted endomorphism's squared basis norms by exact
termwise equality with the existing Haar operator's summable sequence.

The data-bearing owner
`cc20GlobalLogWindowRestrictedL2BasisHilbertSchmidtData` and theorem
`cc20GlobalLogWindowRestrictedL2PositiveTrace_re_nonnegative` then give a
nonnegative real part for the ordinary trace of the positive composition on
the restricted carrier.

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

## Boundary

This proves only finite-window regular-kernel Hilbert--Schmidt legality and
positive-composition trace nonnegativity. It does not identify that trace
with the CC20 Weil functional, add the diagonal `-2 Dirac_0` term, prove the
distributional `-2 Id` identity, establish common-window exhaustion, or prove
unconditional RH.
