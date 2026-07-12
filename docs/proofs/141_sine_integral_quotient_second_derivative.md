# Sine-Integral Quotient Second Derivative

Date: 2026-07-12

Status: accepted local differential foundation; not a `K_I` owner and not an
RH proof.

## Results

`SineIntegral.lean` now proves, for `x != 0`:

```text
HasDerivAt Real.sinc
  ((cos x * x - sin x) / x^2) x

HasDerivAt (deriv sineIntegralQuotient)
  (sineIntegralQuotientSecondDerivativeProfile x) x
```

The first statement uses `sinc = sin / id` away from zero and the quotient
rule. The second differentiates the already-proved quotient derivative, using
the FTC derivative of `sineIntegral` and the derivative of `x^2`.

## Verification

The isolated WSL2 ext4 build of
`ConnesWeilRH.Source.CC20Concrete.SineIntegral` passes. The import audit prints
only `propext`, `Classical.choice`, and `Quot.sound` for these declarations.

## Remaining gate

The second derivative of the full `cc20DeltaRegular` profile still needs the
two affine chain rules and the square-root/product terms. Only after that can
the explicit `Q(delta)` candidate be assembled. The kernel action and
Hilbert-Schmidt estimate remain independent obligations.

## Route judgment

```text
sinc first derivative: accepted
Si/x second derivative: accepted away from zero
Q(delta) full profile: open
K_I kernel action: open
RH: unproved
```
