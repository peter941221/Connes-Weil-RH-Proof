# CC20 Complex Hilbert--Schmidt Positive Trace

Date: 2026-07-12

## Result

The ordinary compact regular kernel now defines a genuine complex-linear
operator on complex `L²`:

```text
T_C(u)(x) = inner_C K_x u.
```

The section is deliberately the first inner-product argument. Mathlib's
complex inner product is linear in the second argument, so this orientation
makes `T_C` complex-linear. The opposite orientation would be conjugate-linear
and cannot be used in `PositiveTrace.BasisHilbertSchmidtData`.

For every complex Hilbert basis, the squared output norms are summable. The
operator and this proof are packaged as
`cc20CompactComplexBasisHilbertSchmidtData`. Its adjoint composition is
therefore trace-class along that basis, its ordinary trace is the
Hilbert--Schmidt norm square, and its real part is nonnegative through the
existing `PositiveTrace` consumer.

## Same-kernel evidence

For every continuous complex input, Lean proves the pointwise formula

```text
T_C(f)(x) = integral_y (cc20CompactRegularKernel(x,y) : C) * f(y).
```

Thus this is a scalar extension of the existing ordinary real kernel, not a
new unrelated operator or a stored compatibility field.

## Boundary

This closes the complex Hilbert--Schmidt and ordinary positive-trace legality
layer for the regular kernel. It does not identify the operator with source
CC20 `K_I`, account for the diagonal Dirac term, prove the CC20 trace read-off,
control prime/pole/archimedean terms on one test, or prove RH.
