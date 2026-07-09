# Normalized Trace-Amplitude Square Scalar Proof Package

Status: route-evidence proof package for the Phase 1 scalar normalization
blocker.

This package targets the Lean input:

```text
normalizedTraceAmplitudeSquareScalarInputFromTheorems :
  TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract ...
```

It proves the route-evidence statement that the original normalized CC20 trace
amplitude square reads as the same restricted CCM25 scalar used by the route.
It does not prove accepted-source status, Lean theorem status, or RH.

## Fixed Data

Fix the normalized source package and trace front end:

```text
base, common, ccm24
normalizedSeed
remainders, rhExit, bridges
fixedData
traceData
```

Let:

```text
a      = sourceTrace.archimedeanTest
g      = fixed source-backed test
lambda = traceData.lambda
F_g    = g^* * g
```

The target scalar equality is:

```text
traceAmplitude_normalizedSeed(a)^2
  =
NormalizedRestrictedScalarNormalForm(base, common, ccm24,
  normalizedSeed, remainders, rhExit, bridges, fixedData, traceData).
```

In CCM25 notation, the right side is the restricted Weil scalar:

```text
QW_lambda(g,g)
  =
archimedeanTerm(F_g)
  + polePairing(g)
  - restrictedFinitePrimeEvaluatorSum(lambda, F_g).
```

## Evidence

| claim | evidence |
|---|---|
| CC20 normalized support-square trace is the trace amplitude square | `ConnesWeilRH/Route/TraceFrontEnd.lean:2200`, `normalized_cc20_support_square_normal_form_eq_trace_amplitude_square`; `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`, normalized square-trace constructors |
| normalized restricted scalar normal form names the CCM25 restricted package expression | `ConnesWeilRH/Route/TraceFrontEnd.lean:2247`, `NormalizedRestrictedScalarNormalForm` |
| Lean contract target | `ConnesWeilRH/Route/TraceFrontEnd.lean:2324`, `NormalizedTraceAmplitudeSquareScalarContract` |
| support-square scalar contract implies the amplitude-square scalar contract | `ConnesWeilRH/Route/TraceFrontEnd.lean:2396`, `normalizedTraceAmplitudeSquareScalarContractOfSupportSquareScalarNormalForm` |
| CCM25 `QW_lambda(g,g)` reduces to that normal form | `ConnesWeilRH/Route/TraceFrontEnd.lean:2453`, `normalized_qw_lambda_reduces_to_normal_form` |
| narrowed same-scalar read-off contract | `ConnesWeilRH/Route/TraceFrontEnd.lean:2540`, `NormalizedSupportSquareQWLambdaScalarReadOff` |
| same-scalar read-off implies support-square scalar normal form | `ConnesWeilRH/Route/TraceFrontEnd.lean:2583`, `normalizedSupportSquareScalarNormalFormContractOfQWLambdaReadOff` |
| skeleton input still open | `ConnesWeilRH/Dev/UnconditionalSkeleton.lean:898`, `normalizedSupportSquareQWLambdaScalarReadOffFromTheorems` |
| normal-form and amplitude skeleton reducers | `ConnesWeilRH/Dev/UnconditionalSkeleton.lean:908`, `normalizedSupportSquareScalarNormalFormInputFromTheorems`; `ConnesWeilRH/Dev/UnconditionalSkeleton.lean:923`, `normalizedTraceAmplitudeSquareScalarInputFromTheorems` |
| the support-square/no-defect/QW_lambda scalar chain is exactly the B1 trace-scale target | `docs/proofs/trace-scale-compatibility-proof-package.md`, Lemmas 2-4 |
| the no-defect compact-form read-off uses the same test and cutoff | `docs/proofs/fixed-s-no-defect-compact-form-read-off.md`, Lemmas 1-4 |
| manuscript source read-off displays the restricted `QW_lambda` scalar | `docs/manuscripts/connes-weil-rh-proof-draft.md:988-1033` |

## Theorem

For the fixed normalized route data:

```text
NormalizedTraceAmplitudeSquareScalar:
  traceAmplitude_normalizedSeed(a)^2
    =
  QW_lambda(g,g)
    =
  NormalizedRestrictedScalarNormalForm(...).
```

This is the exact statement carried by
`TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract`.

## Proof

The normalized CC20 trace seed is a legal square-trace seed. By its defining
square-trace law:

```text
supportSquareTrace_normalizedSeed(a)
  =
traceAmplitude_normalizedSeed(a)^2.
```

The trace-scale compatibility package fixes the finite-lambda scalar chain for
the same route tuple:

```text
supportSquareTrace_normalizedSeed(a)
  =
NoDefectSourceTrace(S,I,lambda,g)
```

and:

```text
NoDefectSourceTrace(S,I,lambda,g)
  =
QW_lambda(g,g).
```

The fixed-S no-defect compact-form package supplies the second equality. It
uses the same convolution square:

```text
F_g = g^* * g
```

and the same restricted interval:

```text
[lambda^(-1), lambda].
```

CCM25 then reads:

```text
QW_lambda(g,g)
  =
archimedeanTerm(F_g)
  + polePairing(g)
  - restrictedFinitePrimeEvaluatorSum(lambda, F_g).
```

By definition, this last scalar is
`NormalizedRestrictedScalarNormalForm(...)` in the Lean route layer.

Combining the equalities gives:

```text
traceAmplitude_normalizedSeed(a)^2
  =
NormalizedRestrictedScalarNormalForm(...).
```

## Lean Import Shape

The proof should discharge the single skeleton input:

```lean
def normalizedTraceAmplitudeSquareScalarInputFromTheorems :
    TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems
```

The Lean theorem should not consume
`NormalizedSupportSquareQWLambdaSourceComparison`; that would make the proof
circular. It should consume a source or proof-package interface equivalent to:

```text
supportSquareTrace_normalizedSeed(a) = QW_lambda(g,g)
```

with the same `a`, `g`, `lambda`, and CCM25 arithmetic package as
`traceData`.

Current Lean status:

```text
normalizedSupportSquareQWLambdaScalarReadOffFromTheorems
        |
        v
normalizedSupportSquareScalarNormalFormInputFromTheorems
        |
        v
normalizedTraceAmplitudeSquareScalarInputFromTheorems
```

The first arrow is implemented by
`normalizedSupportSquareScalarNormalFormContractOfQWLambdaReadOff`. The second
arrow is implemented by
`normalizedTraceAmplitudeSquareScalarContractOfSupportSquareScalarNormalForm`.
The first line is still the mathematical source/import row.

A useful Lean-facing split is:

```text
NormalizedSupportSquareQWLambdaScalarReadOff
  supportSquareTrace_normalizedSeed(a) = QW_lambda(g,g)

normalizedTraceAmplitudeSquareScalarContractOfReadOff
  NormalizedSupportSquareQWLambdaScalarReadOff
    ->
  NormalizedTraceAmplitudeSquareScalarContract
```

The second theorem should be local Lean algebra. It composes:

```text
supportSquareTrace = traceAmplitude^2
QW_lambda = NormalizedRestrictedScalarNormalForm
```

The first theorem is the real mathematical import/proof-package row.

## Remaining Certification Boundary

This package closes the route-evidence version of the normalized scalar
amplitude bridge. Accepted-source certification remains open until a reviewer
accepts the CC20 support-square trace normalization and the CCM25 restricted
read-off with the same fixed test, cutoff, pole convention, and finite-prime
normalization.
