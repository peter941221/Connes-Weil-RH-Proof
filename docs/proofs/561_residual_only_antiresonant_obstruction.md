# Proof 561: residual-only antiresonant obstruction

## Result

The residual-only shortcut is now formalized as an exact scalar spectral-fibre
no-go.  With the antiresonant unitary fibre `U=-I` and coefficient `a=1/2`,

```text
E = I - a U       = (3/2) I
P = (1-a) E^{-1} = (1/3) I
T = (1+a)^{-1}E = I
Q = I + U        = 0.
```

Hence

```text
P - T = -(2/3) I,
```

and no bounded operator `F` can satisfy

```text
P - T = F Q.
```

The Lean owner is
`CCM24FiniteSCompletedJuliaResidualOnlyAntiresonantObstruction.lean`.
The calculation uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Meaning for Gate 3U

This is a spectral fibre, not an assertion that an exact plane wave belongs to
the global `L2` carrier.  It therefore does not disprove a factorization on
the actual Sonin carrier.  It does prove that the physical transport residual
cannot be estimated through the ambient antiresonant loss by an abstract
operator argument alone.

The only remaining valid source target is the complete signed raw row:

```text
Schur boundary row + physical coframe residual
```

with the moving-boundary channel retained before any norm or absolute value.
The Gate 3U estimate, finite-S sign, Burnol identity, and RH remain open.
