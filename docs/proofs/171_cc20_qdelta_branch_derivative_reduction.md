# Proof 171: Q-delta branch-derivative reduction

## Result

Useful analytic reduction, but not an RH proof.

The planned whole-line `L1` route is not justified by the existing CC20
formula. After the logarithmic change of variables, the ordinary kernel is a
convolution profile, but its large-rho behavior contains oscillatory terms from
the sine integral. The correct next object is therefore a Fourier multiplier
or oscillatory convolution distribution, not an assumed absolutely integrable
kernel.

## What is proved in Lean

For `rho > 0`, `RegularKernelCandidate.lean` now proves:

```text
QDeltaRegularCandidate(rho)
  = -4 * rho * sqrt(rho) * DeltaBranchSumDerivative(rho)
    - 2 * rho^2 * sqrt(rho) * DeltaBranchSumSecondDerivative(rho).
```

The proof unfolds the definitions, uses `sqrt(rho)^2 = rho`, and performs the
exact cancellation. In particular, the undifferentiated half-density term
`2 * sqrt(rho) * DeltaBranchSum(rho)` is removed by
`-(rho*d/drho)^2 + 1/4`.

The global log profile already has the exact identity

```text
k(r) = QDeltaRegularExtension(exp(|r|)).
```

so this branch-derivative theorem gives the first explicit formula for the
nonzero log tail without confusing it with the diagonal Dirac term.

`GlobalLogKernel.lean` now transports the same formula to the log profile for
every `r != 0`, so the Fourier-side problem can be stated directly on the
common logarithmic carrier.

## Evidence and boundary

The primary source is Connes--Consani, *Weil positivity and Trace formula, the
archimedean place*, arXiv:2006.13771, formula (10) for `delta(rho)` and the
discussion immediately after formula (11), which introduces
`Q = -(rho d/drho)^2 + 1/4`. Their compactness theorem is for a fixed compact
interval, not for a whole-line `L1` kernel. Direct numerical evaluation of the
formal derivative formula gives `Qdelta(1024) approximately -128.00037`,
consistent with an oscillatory `sqrt(rho)`-scale tail; this numerical
observation is not used as a Lean premise.

The import-facing WSL2 audit reports only:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, RH premise, or stored asymptotic conclusion. RH remains
unproved.

## Remaining bottom

Prove a source-backed Fourier-multiplier bound for the oscillatory profile, or
construct the global operator from the CC20 quantized-calculus representation.
Then identify finite windows as `P_lambda K P_lambda` and continue to the
common three-point bad-space and same-test trace gates.
