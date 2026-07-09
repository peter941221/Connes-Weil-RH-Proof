# Source Common Test And Tuple Theorem Contract

Status: theorem contract for source-object discharge rows 1 and 2.

This file strengthens:

```text
docs/proofs/source-test-convolution-compatibility.md
docs/audits/source-object-theorem-discharge-ledger.md
```

from proof-package and discharge-ledger evidence into formal/import theorem
targets for:

```text
SourceCommonTestAndConvolution(g,F_g)
SourceRouteTupleFixed(S,I,lambda,g)
```

It does not define the analytic CCM24, CCM25, or CC20 test spaces. It fixes
the theorem boundary that must replace the current symbolic `TestFunction`,
`convolutionStar`, and tuple-sharing assumptions before later gates can count
as source-object discharge.

## Boundary

This contract gives stronger evidence than the existing proof package:

```text
proof package
  |
  v
formal/import theorem contract
```

It still gives weaker evidence than a completed proof:

```text
formal/import theorem contract
  |
  v
Lean theorem or accepted source theorem with audited hypotheses
```

The final route cannot treat this contract as discharge. A later source import
or Lean pass must prove these targets.

## Evidence Lock

| item | evidence |
|---|---|
| source-object theorem discharge ledger | `docs/audits/source-object-theorem-discharge-ledger.md` |
| source-object definition contract | `docs/proofs/source-object-definition-theorem-contract.md` |
| source test proof package | `docs/proofs/source-test-convolution-compatibility.md` |
| source-object definition spine | `docs/proofs/source-object-definition-spine-discharge.md` |
| source-object interface plan | `formalization/source-object-interface-plan.md` |
| source-object interface risk audit | `formalization/source-object-interface-risk-audit.md` |

## Top-Level Shape

The future source interface must expose:

```text
CommonTestObject(g,F_g)
RouteTupleObject(S,I,lambda,g)
```

with a bridge:

```text
CommonTestObject(g,F_g)
  ->
RouteTupleObject(S,I,lambda,g)
  ->
SourceObjectPackage(S,I,lambda,g).
```

The package may later project to compact route records, but those records must
not allocate new tests, windows, or lambda parameters.

Blocked shortcut:

```text
test : TestFunction
tupleCompatible : Prop
```

with no named maps from CCM24, CCM25, and CC20 source objects.

## Contract Theorem 1. Common Source Test Object

Target:

```text
SourceCommonTestObject(g,F_g):
  CommonTestObject(g,F_g)
```

Required fields or theorem projections:

```text
sourceTest_g
sourceConvolutionSquare_Fg
sourceConvolutionSquare_eq : F_g = g^* * g
ccm24Test_eq_commonTest
ccm25Test_eq_commonTest
cc20TraceTest_eq_commonTest
cc20MellinTest_eq_commonTest
```

Meaning:

The route must use one test object. CCM24 support transport, CCM25 `QW` and
`QW_lambda`, CC20 trace legality, CC20 Mellin vanishing, and the final sign/RH
exit must all consume that object or a named image of it.

Evidence used:

```text
docs/proofs/source-test-convolution-compatibility.md
docs/audits/source-object-theorem-discharge-ledger.md:87-128
formalization/source-object-interface-plan.md:176-184
```

Reject:

```text
ccm24Test : ...
ccm25Test : ...
cc20TraceTest : ...
cc20MellinTest : ...
```

unless the interface supplies the equality or transport fields above.

## Contract Theorem 2. Convolution Square Ownership

Target:

```text
SourceConvolutionSquareOwned(g,F_g):
  F_g = g^* * g
  and F_g is the source object read by CCM25 finite primes, CC20 trace read-off,
  CC20 Mellin vanishing, and the final sign bridge.
```

Required fields or theorem projections:

```text
convolutionSquare_eq_Fg
ccm25PsiInput_eq_Fg
ccm25RestrictedPrimeSupport_uses_Fg
cc20SupportSquareTrace_uses_Fg
cc20MellinVanishing_uses_Fg
finalSignBridge_uses_Fg
```

Meaning:

`F_g` cannot be a display convention. It must be the owned source object that
travels through the finite-prime, trace, Mellin, and sign legs.

Evidence used:

```text
docs/proofs/source-test-convolution-compatibility.md:51-132
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
docs/proofs/final-sign-bridge-theorem-contract.md
```

Reject:

```text
convolutionStar : TestFunction -> TestFunction -> TestFunction
```

as a primitive route field with no source equality to `F_g`.

## Contract Theorem 3. Fixed Route Tuple

Target:

```text
SourceRouteTupleFixed(S,I,lambda,g):
  every source package consumed by the route is indexed by the same
  (S,I,lambda,g).
```

Required fields or theorem projections:

```text
ccm24Tuple_eq_sourceTuple
ccm25Tuple_eq_sourceTuple
cc20TraceTuple_eq_sourceTuple
cc20ExitTuple_eq_sourceTuple
```

Meaning:

The source-object package must own one route tuple. The compact route-facing
records may project from it, but they cannot choose fresh `S`, `I`, `lambda`,
or `g`.

Evidence used:

```text
docs/proofs/source-object-definition-spine-discharge.md:84-118
docs/proofs/source-object-definition-theorem-contract.md:131-159
docs/audits/source-object-theorem-discharge-ledger.md:131-171
```

Reject:

```text
SemilocalModelSymbols
WeilFormSymbols
ArchimedeanTraceSymbols
FiniteVanishingCriterionPackage
```

constructed from unrelated tuple parameters.

## Contract Theorem 4. Tuple Carries The Window And Square

Target:

```text
SourceTupleCarriesWindowAndSquare(S,I,lambda,g,F_g):
  SourceRouteTupleFixed(S,I,lambda,g)
  ->
  SourceCommonTestObject(g,F_g)
  ->
  the tuple's CCM24 window I and CCM25/CC20 square F_g are the objects used by
  every later source package.
```

Required projections:

```text
tupleWindow_eq_ccm24Window
tupleLambda_eq_qwLambdaParameter
tupleTest_eq_commonTest
tupleSquare_eq_commonSquare
```

Meaning:

Row 1 and Row 2 must compose. A fixed tuple without a common test still permits
test drift. A common test without tuple ownership still permits window and
lambda drift.

Evidence used:

```text
docs/audits/formal-gate-spine-consistency-audit.md:67-124
formalization/source-object-interface-risk-audit.md
```

Reject:

```text
ccm24Window_controls_qwLambda : Prop
```

if it does not consume the same tuple and common test.

## Combined Contract

The formal/import target for rows 1 and 2 is:

```text
SourceCommonTestTupleContract(S,I,lambda,g,F_g):
  SourceCommonTestObject(g,F_g)
  SourceConvolutionSquareOwned(g,F_g)
  SourceRouteTupleFixed(S,I,lambda,g)
  SourceTupleCarriesWindowAndSquare(S,I,lambda,g,F_g)
```

Projection target:

```text
SourceCommonTestTupleContract(S,I,lambda,g,F_g)
  ->
SourceCommonTestAndConvolution(g,F_g)

SourceCommonTestTupleContract(S,I,lambda,g,F_g)
  ->
SourceRouteTupleFixed(S,I,lambda,g)
```

Route consequence:

```text
SourceCommonTestTupleContract(S,I,lambda,g,F_g)
  ->
the later source-object rows may use g, F_g, S, I, and lambda only through this
package or its projections.
```

## Import Acceptance Checklist

A source import can discharge this contract only if it supplies:

| item | required evidence |
|---|---|
| common test | one source test object maps to CCM24, CCM25, and CC20 test uses |
| convolution square | one source equality `F_g=g^* * g` controls finite-prime, trace, Mellin, and sign legs |
| tuple equalities | CCM24, CCM25, CC20 trace, and CC20 exit packages use the same `(S,I,lambda,g)` |
| window and lambda ownership | the tuple window and lambda are the ones used by restricted `QW_lambda` and later window-control rows |
| rejected shortcuts | no standalone `test`, `tupleCompatible`, or compact-record constructors replace the named bridges |

If an import supplies only a broad compatibility proposition, it fails this
contract.

## Lean Interface Consequence

A later Lean interface should expose names matching:

```text
CommonTestObject
RouteTupleObject
SourceCommonTestObject
SourceConvolutionSquareOwned
SourceRouteTupleFixed
SourceTupleCarriesWindowAndSquare
SourceCommonTestTupleContract
```

The interface should keep these bridge names visible on `#print axioms` for
the final route theorem if they remain source assumptions.

## Current Judgment

| question | answer |
|---|---|
| Does this contract define the analytic test spaces? | no |
| Does it specify the formal/import target for Row 1? | yes |
| Does it specify the formal/import target for Row 2? | yes |
| Does it force `F_g=g^* * g` to feed every later leg? | yes |
| Does it prevent tuple drift before Row 3 through Row 7? | yes |
| Does it discharge the source-object definition gate? | no |

Rows 1 and 2 are now import-ready targets. They still require a Lean theorem or
accepted source theorem before the route may treat them as discharged.
