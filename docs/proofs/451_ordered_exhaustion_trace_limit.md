# Proof 451: Ordered exhaustion for the signed trace limit

## Result

Proof 450's all-finsets hypothesis is stronger than the signed Gate 3U scalar
estimate.  For a self-adjoint endpoint, a bound for every finite subset also
forces a uniform bound on the absolute diagonal mass, because positive and
negative indices can be selected separately.

Proof 451 keeps the actual fixed-S
`PositiveTrace.IsTraceClassAlong` witness and only uses the nested natural
Hilbert-basis exhaustion

```text
Finset.range N,  N = 0,1,2,...
```

The partial sums converge to the ordinary diagonal `tsum`.  Therefore the
signed bound on these prefixes is enough to prove the full trace bound, while
preserving cancellations between different diagonal modes.

## Lean interface

The new source module is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSMovingBandExhaustionTrace.lean
```

Its main declarations are:

```lean
ordinaryTraceAlong_re_abs_le_of_rangeDiagonalIntegralBound
ordinaryTraceAlong_norm_le_of_rangeDiagonalIntegralBound
canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_rangeDiagonalBound
```

The canonical consumer now asks for

```text
actual endpoint IsTraceClassAlong on one named basis
  + signed integral bounds only for Finset.range N
  -> support-radius polynomial trace norm bound.
```

This is weaker than Proof 450's bound for arbitrary finite subsets.  It does
not manufacture endpoint trace legality from the uniform bound; that legality
is the fixed-S Gate 3L producer, whose constants may depend on `S`.

## Boundary

Proof 451 does not prove the range-prefix bound.  The remaining analytic
producer must bound the complete recombined moving flow on one ordered basis
exhaustion, retaining the outer, Sonin, prolate, and Gram cancellations.  It
must not replace the signed prefix estimate by diagonal Euler energy or a
primewise total-variation estimate.  Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
