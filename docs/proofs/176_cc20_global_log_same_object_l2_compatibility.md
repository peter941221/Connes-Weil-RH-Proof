# Proof 176: same-object log/Haar L2 compatibility

## Result

For every finite window `lambda > 1`, the continuous-input Haar operator and
the global logarithmic operator refer to the same kernel action and have the
same L2 norm after the coordinate change `rho = exp(t)`.

The new declarations are:

```text
cc20WindowHaarComplexKernelCoefficient_logRestriction
cc20WindowHaarComplexKernelCoefficient_logRestriction_eq
cc20WindowHaarComplexL2Operator_logRestriction
norm_cc20GlobalLogWindowRegularActionToLp_sq
norm_cc20WindowHaarComplexL2Operator_logRestriction_eq_global
```

The proof uses the inverse window point `rho -> log rho`, the previously
proved source-Haar/log interval identity, and the `MemLp.toLp` representative
formula. It does not identify arbitrary Lp representatives pointwise.

## Verification

The WSL2 Lake build passes after rebuilding the changed dependency and the
import-facing audit reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, RH premise, stored operator bound, or Weil-positivity premise
was introduced.

## Boundary

This is still only the continuous-input/window layer. A bounded operator on
the common global L2 carrier, strong convergence under increasing windows,
the three-point bad-space estimate, the diagonal `-2 Dirac_0 -> -2 Id` limit,
the same-test trace read-off, and RH remain open. Finite-window compactness
still does not imply whole-line compactness or an L1 Fourier multiplier bound.
