# CC20 compact-interval kernel operator

The ordinary kernel `cc20RegularKernelReal` is now proved continuous on all
real coordinates by composing the positive-coordinate kernel with the
continuous map `x |-> max x (1/2)`. For every continuous real function `f`,
the fixed-interval formula

```text
(T f)(x) = integral from 1/2 to 2 of K(x,y) f(y) dy
```

is proved continuous using Mathlib's parametric interval-integral theorem.
The same object is packaged as a linear map on `ContinuousMap ℝ ℝ`; additivity
uses interval-integral linearity and continuity-based interval integrability,
and scalar homogeneity uses interval-integral scalar linearity.

This is an axiom-clean operator construction, audited in
`Dev/RegularKernelOperatorAudit.lean`. It does not establish an `L2`
extension, Hilbert--Schmidt property, CC20 `K_I` action identity, trace
read-off, or any unconditional RH implication.
