# Proof 188: Selected single-crossing prime-power read-off

## Result

`SelectedSingleCrossing.lean` formalizes the coefficient calculation from
proof 038 on the existing `SelectedWeilSquareOwner`.

For a translation length `b`, the paired crossing diagonal is integrated over
the crossing interval:

```text
singleCrossingPairDiagonalIntegral owner b
  = integral_(0..b)
      (F(b) + F(-b)) dx,

F = owner.convolutionSquare.test.
```

Lean proves the exact geometric read-off

```text
singleCrossingPairDiagonalIntegral owner b
  = b * (F(b) + F(-b)).
```

For a prime `p` and nonzero natural exponent `m`, applying the Euler-log
coefficient before inserting the crossing length gives

```text
(1 / (m * sqrt(p^m)))
  * singleCrossingPairDiagonalIntegral owner (m * log p)
  = owner.finitePrimeTerm (p^m).
```

The proof uses Mathlib's exact identities
`vonMangoldt_apply_pow`, `vonMangoldt_apply_prime`, and `Real.log_pow`.
Both sides therefore use the same stored convolution square; there is no
evaluation witness or scalar read-off field.

The auxiliary identity
`inv_sqrt_nat_pow_eq_rpow` also rewrites the coefficient literally as

```text
p^(-m/2) / m,
```

using Mathlib's real `rpow` laws, so the normalization is not merely an
informal `sqrt(p^m)` abbreviation.

## Lean declarations

```text
SelectedWeilSquareOwner.singleCrossingPairDiagonalIntegral
SelectedWeilSquareOwner.singleCrossingPairDiagonalIntegral_eq
SelectedWeilSquareOwner.eulerLogSingleCrossingAtom
SelectedWeilSquareOwner.eulerLogSingleCrossingAtom_eq_finitePrimeTerm_pow
```

## Verification

The retained-cache WSL builds pass:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.SelectedSingleCrossing  2917/2917
lake build ConnesWeilRH.Source.CCM25Concrete                         2966/2966
```

`SelectedSingleCrossingAudit.lean` imports the public module, prints every
declaration, and reports only:

```text
propext
Classical.choice
Quot.sound
```

## Route boundary

This closes the scalar diagonal-kernel and prime-power normalization part of
the local crossing calculation. It does not yet construct the half-line
partial-translation operator on `L2`, prove that the smoothed composition is
trace class, or identify its basis trace with this diagonal integral.

Consequently it is not a finite-S positive-trace owner, does not repair the
rejected endpoint metric projection, and does not prove RH. The next exact
bottom is the operator-trace equality for the same selected square.
