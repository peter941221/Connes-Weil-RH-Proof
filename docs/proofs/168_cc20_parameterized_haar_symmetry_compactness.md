# CC20 Parameterized Haar Symmetry And Compactness

Date: 2026-07-12

Status: finite-window symmetry, compactness, and bad-space sign accepted;
common-domain exhaustion and CC20 trace read-off remain open.

## Result

For every `lambda > 1`, the ordinary CC20 regular-kernel operator

```text
K_lambda : L2([1/lambda,lambda], d rho/rho; C)
  -> L2([1/lambda,lambda], d rho/rho; C)
```

is now proved symmetric and compact.

`ParameterizedHaarSymmetry.lean` first transports the underlying pointwise
identity

```text
k_lambda(x,y) = k_lambda(y,x)
```

through the product Haar integral using Fubini.  Density of continuous
functions then gives

```text
inner (K_lambda u) v = inner u (K_lambda v)
```

for all `L2` inputs.

This symmetry is proved for the genuine positive-coordinate kernel on every
window.  It does not pass through the fixed-window real-coordinate clamp.

`ParameterizedHaarCompact.lean` sends the `L2` unit ball to bounded continuous
coefficient functions.  Continuity of the kernel-section map gives
equicontinuity, the `L2` coefficient estimate gives pointwise boundedness, and
Arzela--Ascoli gives compactness after returning to `L2`.

The declaration

```text
exists_finiteDimensional_cc20WindowHaarRegularRemainder_nonpositive
```

therefore supplies, for each window, a finite-dimensional control space whose
orthogonal complement satisfies

```text
Re inner(x, (K_lambda - 2 Id)x) <= 0.
```

## Route Meaning

The finite-window analytic package is now complete at the ordinary regular
kernel level:

```text
exact source Haar measure
  -> Hilbert--Schmidt regular-kernel operator
  -> symmetric compact operator
  -> finite-dimensional bad-space sign for K_lambda - 2 Id
```

The control space may depend on `lambda`.  Nothing here proves that it is the
span of the route's three Mellin evaluation vectors, that these vectors live
in a common global form domain, or that the window traces converge to the
CC20 Weil functional.

## Verification

Using the retained WSL2 Lake cache, these commands passed:

```text
lake build ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarSymmetry
lake build ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarCompact
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/ParameterizedHaarCompactAudit.lean
```

The focused declarations print only:

```text
propext
Classical.choice
Quot.sound
```

Their complete printed types contain only the window parameter, its
`lambda > 1` proof, and the expected Hilbert-space inputs.  No RH premise,
Weil-positivity premise, or `sorryAx` occurs.

## Route Judgment

```text
finite-window symmetry: accepted
finite-window compactness: accepted
finite-window bad-space sign: accepted
uniform/common-domain bad-space control: open
same-test CC20 trace/read-off: open
RH: unproved
```
