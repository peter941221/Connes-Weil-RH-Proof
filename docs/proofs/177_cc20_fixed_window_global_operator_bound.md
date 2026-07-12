# Proof 177: fixed-window bound on the common log-L2 carrier

## Result

For each `lambda > 1`, continuous inputs restricted to the logarithmic window
now have a common-carrier `Lp` representative and an exact norm identity.
The finite Haar operator therefore yields the genuine estimate

```text
‖globalWindowActionToLp(lambda, u)‖
  ≤ ‖parameterizedHaarOperator(lambda)‖
    * ‖globalWindowInputToLp(lambda, u)‖.
```

The input and output use the same `volume`-based global `Lp C 2` carrier. The
proof transports both norms through `rho = exp(t)` and uses the existing
continuous-input Haar operator bound.

## Verification

The WSL2 incremental build of `GlobalLogKernel` passes. The import-facing
audit is axiom-clean with only:

```text
propext
Classical.choice
Quot.sound
```

No whole-line `L1` estimate, RH premise, stored conclusion, `sorry`, or
`admit` was introduced.

## Boundary

The bound is still stated on the continuous-input core and its constant
depends on the finite window. The remaining extension problem is to identify a
dense common-carrier core and extend each fixed-window map, then prove strong
compatibility as windows increase. This does not yet prove the diagonal
distributional limit, the three-point bad-space estimate, the same-test trace
read-off, or RH.
