# Proof 191: Single-Crossing Trace Identity Verdict

This verdict is superseded for the compact-kernel layer by
`docs/proofs/192_compact_crossing_operator_finite_prime_read_off.md`.
The rank-one rejection below remains valid; the later continuous-kernel
factorization supplies the missing paired operator trace and finite-prime
read-off without reusing the rank-one scalar.

## Result

The direct second-stage continuation from the rank-one producer is rejected.
Two independent defects were identified and formalized.

## Translation direction

The global translation convention is

```text
U_b u(t) = u(t+b).
```

Therefore the positive-length crossing is

```text
J_b = (I-P_+) U_b P_+.
```

For `b>0`, this maps `[0,b)` into `[-b,0)`. The earlier `U_(-b)` draft is zero
for nonnegative `b`, so it cannot represent the prime-power length
`b=m*log(p)`. `cc20SingleCrossingOperator` now uses the forced `U_b` direction.

## Rank-one trace

The first-stage smoother is exactly

```text
J_b o rankOne(k,h) = rankOne(J_b k,h).
```

For every Hilbert basis, Lean proves

```text
ordinaryTraceAlong (J_b o rankOne(k,h)) = <h,J_b k>.
```

The proof uses `HilbertBasis.tsum_inner_mul_inner`; it stores no trace value.
For the canonical source specialization, both vectors are the same
`cc20LogPullbackLp p`.

This trace is not the selected diagonal scalar

```text
b * (F(b) + F(-b)).
```

The latter belongs to the convolution-smoothed operator `C_h* C_h J_b`, not
to a rank-one smoothing. Thus the rank-one producer is sufficient for minimal
trace-class legality but cannot discharge the prime read-off.

## Correct trace-class bottom

`PositiveTrace.BasisHilbertSchmidtPairData` now packages two operators `A,B`
with a common source basis and independently proved square-summable images.
Lean proves that the diagonal series of `A* B` is absolutely summable from

```text
|<Ae_i,Be_i>|
  <= ||Ae_i|| ||Be_i||
  <= (||Ae_i||^2 + ||Be_i||^2)/2.
```

This is the correct ordinary trace-class layer for the future factorization
of `C_h* C_h J_b`. It does not yet construct the global convolution operator
or prove the kernel-diagonal integral theorem.

## Route judgment

```text
rank-one trace -> selected prime diagonal: rejected
translation direction: corrected to U_b
two-Hilbert-Schmidt product legality: proved
Schwartz translation-section operator: open
basis trace -> diagonal kernel integral: open
RH: open
```
