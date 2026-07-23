# Proof 503: route/polar kernel normal form

## 1. Result

The result is good for an exact normal form of the route/polar ordering
residual.  It does not prove the required coherence equation, Gate 3U, the
finite-S sign, or RH.

```text
+------------------------------------------------------+------------------+
| item                                                 | status           |
+------------------------------------------------------+------------------+
| route target response                                | explicit         |
| base detector response                               | explicit         |
| route/polar kernel                                   | explicit         |
| local ordering residual as kernel defect             | proved           |
| non-polar gap as first jet plus kernel defect        | proved           |
| adjacent route/polar coherence equation              | isolated         |
| coherence producer                                   | still open       |
| Gate 3U / finite-S sign / Burnol identity / RH       | still open       |
+------------------------------------------------------+------------------+
```

The Lean owner is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRouteKernelNormalForm.lean
```

## 2. Why a new kernel is necessary

Proof 502 already identifies the unresolved local term as

```text
NonpolarGap(p,S)=FirstJet(p,S)+OrderingResidual(p,S).
```

The route endpoint is built from the unpolarized target frame and its ordered
Gram correction.  The relative numerator is built from the adjacent polar
compression.  These are not definitionally the same response, so the
ordering residual cannot be silently treated as a polar numerator.

Proof 503 records their exact difference in one source-carrier operator:

```text
RouteTarget(S)
  =TargetFrameRoot(S)^dagger TargetDualRoot(S),

BaseDetector
  =BaseRoot^dagger BaseRoot,

RoutePolarKernel(S)
  =BaseDetector+PolarCompression(S)-RouteTarget(S).
```

The operator is defined by
`suffixActualBandRoutePolarKernel`.

## 3. Local normal form

For

```text
F_(p,S)=suffixEulerFrameTransition(lambda,p,S),
R_(p,S)=suffixEulerFrameReverseTransition(lambda,p,S),
rho_p=primeSchurMarkovScalar(p),
```

Lean proves the operator identity

```text
OrderingResidual(p,S)
 =F_(p,S) RoutePolarKernel(S) R_(p,S)
   -rho_p RoutePolarKernel(p::S).
```

This is an identity before trace, norm, or any absolute value.  The proof
expands the formal `relativeNumerator`, the endpoint `BaseDetector-RouteTarget`
form, and continuous-linear-map composition, then closes the remaining
commutative scalar algebra.

The corresponding unresolved gap is therefore exactly

```text
NonpolarGap(p,S)
 =FirstJet(p,S)
  +F_(p,S) RoutePolarKernel(S) R_(p,S)
  -rho_p RoutePolarKernel(p::S).
```

## 4. Exact coherence condition

The residual vanishes if and only if the concrete kernel obeys the adjacent
Schur--Markov coherence equation

```text
F_(p,S) RoutePolarKernel(S) R_(p,S)
  =rho_p RoutePolarKernel(p::S).
```

Lean ownership:

```text
suffixActualBandLocalRoutePolarOrderingResidual_eq_zero_iff_kernel_coherent
```

This is an exact equivalence, not an assumption that the equation holds.
Neither the current route target nor the polar compression has a proved
family-uniform coherence theorem.

## 5. Gate 3U boundary

The active chain is now

```text
[actual left Julia co-defect]
             |
             +--> polar Julia term                 proved in Proof 502
             |
             +--> non-polar gap
                       |
                       +--> first jet + kernel defect   exact in Proof 503
                                  |
                                  +--> kernel coherence or a common
                                      left-co-defect factorization   open
```

Do not set the ordering residual to zero from the coherence equivalence, and
do not estimate the first jet and kernel defect separately before a
same-object source bound is available.  The finite-S sign, negative-owner
integration, Burnol identity, and `_root_.RiemannHypothesis` remain open.

## 6. Verification contract

The focused audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRouteKernelNormalFormAudit.lean
```

The Ubuntu 24.04 WSL2 acceptance batch passed:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 503 focused axiom audit            |  3320 | PASS   |
| CCM25Concrete aggregate                  |  3780 | PASS   |
| full repository                           |  3861 | PASS   |
+------------------------------------------+-------+--------+
```

The audit reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

for the four principal theorems, with no `sorry`, `admit`, or user axiom.
