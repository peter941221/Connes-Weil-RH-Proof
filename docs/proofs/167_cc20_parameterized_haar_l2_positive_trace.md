# CC20 Parameterized Haar L2 And Positive Trace

Date: 2026-07-12

Status: finite-window regular-kernel Hilbert--Schmidt and positive-trace layer
accepted; exhaustion trace and CC20 read-off remain open.

## Result

For every `lambda > 1`, Lean now places the ordinary CC20 regular kernel on
the exact source Hilbert space

```text
L2([1/lambda, lambda], d rho/rho; C).
```

The same kernel section defines the continuous linear operator
`cc20WindowHaarComplexL2Operator`.  On continuous inputs,
`cc20WindowHaarComplexKernelCoefficient_continuous_input` identifies this
operator with the explicit Haar integral action.

The window lower bound and `lambda > 1` construct each coordinate directly as
a `PositiveCoordinate`.  The kernel then calls `cc20RegularKernel` itself.
The fixed `[1/2,2]` wrapper `cc20RegularKernelReal`, which clamps smaller
coordinates to `1/2`, is not used in this parameterized chain.

For every complex Hilbert basis, the finite-basis Bessel estimate gives

```text
sum_i ||K_lambda e_i||^2 < infinity.
```

The declarations

```text
cc20WindowHaarComplexL2Operator_basis_normSq_summable
cc20WindowHaarComplexBasisHilbertSchmidtData
cc20WindowHaarComplexPositiveTrace_re_nonnegative
```

therefore package the same operator as Hilbert--Schmidt data and prove that
the real part of the ordinary trace of `K_lambda^* K_lambda` is nonnegative.

Source module:

```text
ConnesWeilRH/Source/CC20Concrete/ParameterizedHaarL2.lean
```

## Route Meaning

The accepted finite-window chain is now:

```text
positive compact source test
  -> support in one [1/lambda, lambda]
  -> exact Haar space with measure d rho/rho
  -> same regular-kernel L2 operator
  -> Hilbert--Schmidt positive composition and nonnegative trace
```

This does not identify the positive composition trace with the CC20 Weil
functional.  It also does not include the diagonal `-2 Dirac_0` term, prove
its `-2 Id` quadratic-form realization, or compare operators living in
different window Hilbert spaces.

## Verification

The existing WSL2 Lake cache was retained while synchronizing only the
Windows source tree.  These commands passed:

```text
lake build ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarL2
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/ParameterizedHaarL2Audit.lean
```

The focused declarations print only:

```text
propext
Classical.choice
Quot.sound
```

Their complete printed types contain the expected window, positivity proof,
and Hilbert basis parameters; no RH premise, Weil-positivity premise, or
`sorryAx` occurs.

## Route Judgment

```text
parameterized regular-kernel L2 operator: accepted
parameterized Hilbert--Schmidt summability: accepted
finite-window positive-composition trace: accepted
cross-window compatibility and exhaustion: open
same-test CC20 trace/read-off: open
RH: unproved
```
