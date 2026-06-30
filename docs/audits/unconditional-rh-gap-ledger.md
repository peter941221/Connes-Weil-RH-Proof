# Unconditional RH Gap Ledger

Status: working ledger for turning the certificate-conditional Lean theorem into
an unconditional theorem.

## Result

Bad result for the final objective:

```text
The repository still does not prove _root_.RiemannHypothesis unconditionally.
```

Good result for route engineering:

```text
The current Lean route has isolated the remaining work into explicit certificate
and source-object inputs instead of hiding them as route-local axioms.
```

The next phase should not optimize the shape of already-visible interfaces
unless the edit removes, weakens, or proves one of the inputs listed below.

## Current Lean Boundary

The final theorem has the conditional shape:

```lean
theorem final_connes_weil_rh
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    _root_.RiemannHypothesis
```

Evidence:

| object | evidence |
|---|---|
| final theorem consumes a certificate | `ConnesWeilRH/Route/RouteTheorem.lean:801-808` |
| certificate fields | `ConnesWeilRH/Route/RouteTheorem.lean:22-25` |
| route inputs are CCM24/CCM25/CC20 interfaces | `ConnesWeilRH/Route/Definitions.lean:31-34` |
| expanded source package constructor still requires front-end evidence | `ConnesWeilRH/Route/RouteTheorem.lean:653-665` |
| route bridge certificate fields | `ConnesWeilRH/Route/Bridge.lean:2767-2780` |

So the current proof graph is:

```text
RouteCertificate inputs
        |
        v
cc20_source_rh_of_route_certificate
        |
        v
RHDefinitionBridge.source_rh_to_mathlib_rh
        |
        v
_root_.RiemannHypothesis
```

The missing unconditional graph is:

```text
concrete source definitions / accepted imports / Lean analytic proofs
        |
        v
SourceObjectPackage
        |
        v
ExpandedSourceFixedSTestFrontEnd
        |
        v
ExpandedSourceTraceReadOffFrontEnd
        |
        v
ExpandedSourceRouteCertificateFrontEnd
        |
        v
RouteCertificate (RouteInputs.ofExpandedSourcePackage pkg)
        |
        v
_root_.RiemannHypothesis
```

## Evidence Scale

Use this scale for every remaining assumption:

| color | meaning | action |
|---|---|---|
| Green | definitional projection or local Lean theorem already available | replace the assumption now |
| Yellow | theorem target is local and exact, but still needs Lean proof work | create/prove the local theorem |
| Red | real external or analytic theorem remains | formalize/import/prove before claiming unconditional RH |

Proof-package coverage is not Green. A proof package can justify the theorem
target, but it does not remove the Lean input until the exact theorem is
formalized or imported.

## Top-Level Gaps

| gap | current holder | status | why it blocks unconditional RH | next action |
|---|---|---|---|---|
| Build `SourceObjectPackage` without assumptions | `ConnesWeilRH/Source/Objects.lean:143-157` | Red | this package owns the common test, CCM24 objects, CCM25 rows, CC20 trace objects, CC20 RH exit, and cross-object equalities | replace broad `Prop` fields by concrete definitions or accepted theorem interfaces row by row |
| Build `ExpandedSourceFixedSTestFrontEnd` | `ConnesWeilRH/Route/Definitions.lean:46-61` | Yellow/Red | it supplies admissibility, triple vanishing, source triple-vanishing symbols, and finite-prime visibility for the fixed test | split definitional bridges from analytic visibility and prove the definitional bridges first |
| Build `ExpandedSourceTraceReadOffFrontEnd` | `ConnesWeilRH/Route/Theorem1.lean` source-package front-end constructors | Red | it supplies the fixed trace read-off data, lambda, and CCM25 arithmetic package used by the bridge | derive only after common-test and CCM25 fixed-lambda arithmetic are concrete |
| Build `ExpandedSourceRouteCertificateFrontEnd` | `ConnesWeilRH/Route/RouteTheorem.lean:84-112` | Red | it supplies sign/defect classification, restricted-to-full scalar equality, and final sign bridge | attack after source-object/common-test and trace read-off are stable |
| Remove `RouteCertificate` parameter from final theorem | `ConnesWeilRH/Route/RouteTheorem.lean:351-358` | Red | this is the final step; removing it before the above constructors are proved would be a false unconditional claim | only add an unconditional theorem after the constructors exist and pass axiom audit |

## Phase 0/1 Update, 2026-06-30

Phase 0 is complete: the conditional theorem boundary is preserved. The final
route theorem remains
`final_connes_weil_rh {inputs : RouteInputs} (cert : RouteCertificate inputs)`,
and no imported no-argument `unconditional_rh` theorem has been added.

Phase 1 is not complete at Lean or accepted-source level. The mathematical
route now has a proof-package target:

```text
docs/proofs/normalized-trace-amplitude-square-scalar-proof-package.md
```

That package gives the route-evidence chain:

```text
traceAmplitude(a)^2
        =
supportSquareTrace(a)
        =
NoDefectSourceTrace(S,I,lambda,g)
        =
QW_lambda(g,g)
        =
NormalizedRestrictedScalarNormalForm(...)
```

The current Lean-backed pieces are:

| row | evidence |
|---|---|
| CC20 support-square trace is the normalized trace-amplitude square | `ConnesWeilRH/Route/TraceFrontEnd.lean:2200` |
| shared normalized restricted scalar normal form | `ConnesWeilRH/Route/TraceFrontEnd.lean:2247` |
| skeleton contract target | `ConnesWeilRH/Route/TraceFrontEnd.lean:2324` |
| support-square scalar contract implies amplitude-square scalar contract | `ConnesWeilRH/Route/TraceFrontEnd.lean:2396` |
| CCM25 `QW_lambda` reduces to that normal form | `ConnesWeilRH/Route/TraceFrontEnd.lean:2453` |
| same-scalar read-off is now the narrowed Lean input | `ConnesWeilRH/Route/TraceFrontEnd.lean:2540`, `NormalizedSupportSquareQWLambdaScalarReadOff` |
| read-off implies support-square scalar normal-form contract | `ConnesWeilRH/Route/TraceFrontEnd.lean:2583`, `normalizedSupportSquareScalarNormalFormContractOfQWLambdaReadOff` |
| CC20 normalized seed source no-defect trace reduces locally to `traceAmplitude g ^ 2` | `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean:321` |

The remaining Phase 1 Lean blocker is now exact:

```text
traceAmplitude(g)^2
  =
NormalizedRestrictedScalarNormalForm(...)
```

The open skeleton input has been narrowed again to the same-scalar read-off:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:898
normalizedSupportSquareQWLambdaScalarReadOffFromTheorems
```

`normalizedSupportSquareScalarNormalFormInputFromTheorems` and
`normalizedTraceAmplitudeSquareScalarInputFromTheorems` are now reducers built
from this read-off.

To close the narrowed input in Lean, add a source theorem or proof-package
interface proving the same-scalar support-square read-off:

```text
supportSquareTrace_normalizedSeed(a) = QW_lambda(g,g)
```

for the same `a`, `g`, `lambda`, and CCM25 arithmetic package carried by
`traceData`. Do not consume `NormalizedSupportSquareQWLambdaSourceComparison`
to prove this row; that comparison is downstream of the scalar bridge and
would make the proof circular.

The top-level source package skeleton has also been split:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:26
SourceObjectPackageInputData
```

`sourceObjectPackageFromTheorems` now uses
`Source.sourceObjectPackageOfData` instead of being a direct broad `sorry`.
This removes one black-box package assumption, but the data fields inside
`SourceObjectPackageInputData` still need source theorem evidence.

## Phase 2 Scalar Slice Update, 2026-06-30

Result: partial Phase 2 progress, not an unconditional RH proof.

| item | evidence |
|---|---|
| concrete scalar CC20 trace seed | `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`, `ScalarTraceScaleSymbols` |
| normalized scalar CC20 trace seed | `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`, `NormalizedScalarTraceScaleSymbols` |
| scalar no-defect read-off | `NormalizedScalarTraceScaleSymbols.source_no_defect_trace_eq_scalar` |
| scalar trace-object package constructor | `normalizedScalarTraceObjectPackage` |
| package scalar read-off | `normalized_scalar_trace_object_source_no_defect_eq_scalar` |

What this proves:

```text
sourceNoDefectTrace(g) = scalarTrace(g)
supportSquareTrace(g) = scalarTrace(g)
0 <= positiveTrace(g)
```

for the scalar-normalized CC20 seed, with positivity supplied by the theorem
`scalarTrace_nonnegative`.

Why Phase 1 is still not Green:

```text
CC20 source package
    |
    v
fixedData + traceData
    |
    v
NormalizedRestrictedScalarNormalForm(lambda, ccm25ArithmeticPackage)
```

The existing source package is constructed before the downstream
`TraceFrontEndData.lambda` and `traceData.ccm25ArithmeticPackage` values exist.
Therefore the current normalized package path cannot definitionally set its
CC20 scalar to `NormalizedRestrictedScalarNormalForm`. The new proof package
selects the other route: prove the old amplitude-square seed equals the CCM25
restricted normal form through the support-square/no-defect/`QW_lambda`
read-off chain.

Remaining acceptable routes:

| route | status |
|---|---|
| formalize/import the proof-package chain for the old amplitude-square seed | current target |
| add a scalar-normalized package/front-end path where the fixed-lambda CCM25 scalar is available before CC20 package construction | fallback |
| add a free equality field | rejected |

## Source-Object Field Gaps

The source-object layer is the first real battlefield because all compact
interfaces project from it.

| field group | evidence | status | blocking reason | next target |
|---|---|---|---|---|
| common test and convolution square | `ConnesWeilRH/Source/Objects.lean:24-41` | Yellow/Red | `sourceConvolutionSquareReadOff` is now a Lean equality against the CCM25 convolution square, the common CCM25 source-test interface is tied to arithmetic rows, and source involution is now a named bridge record; the involution bridge itself remains an input | continue replacing bridge-record fields by exact source/import theorems |
| CCM24 fixed-S semilocal object | `ConnesWeilRH/Source/Objects.lean:30-72` | Red | fixed Hilbert model, support transport, bounded comparison, and Sonin exhaustion are analytic CCM24 inputs | formalize/import the CCM24 fixed-S model and transport theorem |
| CCM25 Weil object | `ConnesWeilRH/Source/Objects.lean:74-77` | Yellow/Red | the concrete arithmetic rows are now structured, but exact source definitions for `QW`, `QW_lambda`, support, weights, pairing, and pole remain theorem inputs | continue replacing finite-prime symbolic data by support-scoped concrete definitions |
| CC20 trace object | `ConnesWeilRH/Source/Objects.lean:79-118` | Red | Hilbert-Schmidt, trace-class, cyclicity, support-square trace, remainder, and sign data are analytic CC20 inputs | first formal target: trace legality and no-defect read-off with exact hypotheses |
| CC20 RH exit object | `ConnesWeilRH/Source/Objects.lean:120-141` | Red | Proposition C.1, Mellin vanishing, final sign, and source-RH-to-Mathlib bridge must be exact | keep final-exit theorem contract separate from route-local density claims |
| cross-object equalities | `ConnesWeilRH/Source/Objects.lean:36-91,167-176` | Yellow/Red | the route still needs one `g`, one `F_g`, one window, and one sign convention across CCM24/CCM25/CC20; CCM24 and CC20 compatibility are now named bridge records with inspectable support, Fourier, convolution-support, trace, and Mellin legs | next attack the bridge-record fields, especially `sourceTestCompatibility`, `traceLegIsCommonTest`, and `mellinLegIsCommonTest` |

## Interface Gaps

The compact source interfaces expose the current formal boundary.

| interface | evidence | remaining red rows |
|---|---|---|
| CCM24 | `ConnesWeilRH/Source/CCM24.lean:53-59` | canonical semilocal model, support transport, bounded comparison, Sonin comparison |
| CCM25 | `ConnesWeilRH/Source/CCM25.lean:55-61` | `QW`/`Psi` definitions, restricted `QW_lambda`, finite-prime normalization, pole normalization |
| CC20 | `ConnesWeilRH/Source/CC20.lean:119-130` | trace square, trace-class template, Mellin convention, sign normalization, finite-vanishing RH exit package |

The projection theorems from source objects are useful but not sufficient:

```text
SourceObjectPackage -> CCM24Interface
SourceObjectPackage -> CCM25Interface
SourceObjectPackage -> CC20Interface
```

Evidence:

| projection | evidence |
|---|---|
| CCM24 projection | `ConnesWeilRH/Source/CCM24.lean:63-73` |
| CCM25 projection | `ConnesWeilRH/Source/CCM25.lean:65-82` |
| CC20 projection | `ConnesWeilRH/Source/CC20.lean:204-219` |

These projections are Green only after `SourceObjectPackage` itself is built
from concrete definitions, accepted imports, or Lean analytic proofs.

## First Attack Slice

Attack the smallest slice that improves the unconditional theorem rather than
only polishing interfaces:

```text
Source common test and convolution compatibility
        |
        v
fixed route tuple uses the same g, F_g, S, I, lambda
        |
        v
CCM25 fixed-lambda finite-prime support and term normalization
        |
        v
restricted-to-full scalar equality for the same fixed test
```

Why this comes first:

| reason | consequence |
|---|---|
| every downstream bridge uses the same test object | a mismatch here invalidates CCM24 transport, CCM25 read-off, CC20 Mellin conversion, and final sign |
| recent Lean work already made finite-prime sums support-scoped | this gives a concrete foothold for reducing symbolic CCM25 assumptions |
| restricted-to-full is fixed-test scalar equality | proving it requires common test, window containment, and finite-prime support stabilization before sign/defect work can be final |

Immediate Green/Yellow candidates:

| candidate | likely status | evidence to inspect next |
|---|---|---|
| turn common-test equality `Prop` fields into named bridge records | Yellow | `ConnesWeilRH/Source/Objects.lean:149-153` and `docs/proofs/source-common-test-tuple-theorem-contract.md` |
| remove old full-`forall n` finite-prime compatibility uses from route-facing CCM25 read-offs | Yellow | `ConnesWeilRH/Source/CCM25Concrete/*` and `ConnesWeilRH/Route/Bridge.lean` recent scoped-sum path |
| prove more package projections from scoped fixed-lambda certificates | Yellow | `ConnesWeilRH/Source/CCM25Concrete/Package.lean` |

Progress note, 2026-06-30:

```text
The fixed-lambda CCM25 package already proves the finite-prime part of the
restricted-to-full comparison:

  source_restricted_finite_prime_evaluator_sum =
  source_global_finite_prime_evaluator_sum.

The remaining scalar full-trace balance is not only this finite-prime equality.
It also needs the archimedean/pole identity

  archimedeanTerm(F_g) + polePairing(g)
    =
  poleFunctional(F_g) - archimedeanTerm(F_g).
```

Evidence:

| item | evidence |
|---|---|
| finite-prime restricted/global equality | `ConnesWeilRH/Source/CCM25Concrete/Package.lean:849` |
| route theorem exposing the finite-prime half | `ConnesWeilRH/Route/TraceFrontEnd.lean`, `normalizedScalarFullTraceArchimedeanFinitePrimeBalance` |
| remaining archimedean/pole contract | `ConnesWeilRH/Route/TraceFrontEnd.lean`, `NormalizedScalarFullTraceArchimedeanPoleBalance` |
| full balance from pole balance plus finite-prime equality | `ConnesWeilRH/Route/TraceFrontEnd.lean`, `normalizedScalarFullTraceArchimedeanBalanceOfPoleBalance` |

Progress note, 2026-06-29:

```text
CommonTestObject now depends on the CCM25 Weil symbols, and
sourceConvolutionSquareReadOff is a concrete equality

  sourceConvolutionSquare = W.convolutionStar sourceTest sourceTest.

Expanded source route construction stores the common tuple at the source square
and transports both restricted-to-full and final-sign route-square uses through
that equality.
```

Evidence:

| item | evidence |
|---|---|
| source-square equality in common test object | `ConnesWeilRH/Source/Objects.lean:24-28` |
| route read-off from source square to CCM25 convolution square | `ConnesWeilRH/Route/RouteTheorem.lean:116-136` |
| common tuple stored at source square | `ConnesWeilRH/Route/RouteTheorem.lean:89-95` |
| restricted-to-full transported to route square | `ConnesWeilRH/Route/RouteTheorem.lean:186-203` |
| final sign transported to route square through common tuple | `ConnesWeilRH/Route/RouteTheorem.lean:205-224` |

Additional progress note, 2026-06-29:

```text
CommonTestObject now carries the CCM25 source-test evaluator interface for the
same source test, and SourceObjectPackage ties that evaluator to the arithmetic
rows by equality.
```

Evidence:

| item | evidence |
|---|---|
| common test carries CCM25 evaluator interface | `ConnesWeilRH/Source/Objects.lean:24-31` |
| source package ties common evaluator to arithmetic rows | `ConnesWeilRH/Source/Objects.lean:150-153` |
| source projection theorem | `ConnesWeilRH/Source/ObjectDerivations.lean:32-45` |
| route-facing projection theorem | `ConnesWeilRH/Route/RouteTheorem.lean:124-137` |

Additional progress note, 2026-06-29:

```text
The remaining cross-object common-test assumptions have been split into named
bridge records instead of anonymous Prop fields:

  CommonTestInvolutionBridge
  CCM24CommonTestBridge
  CC20CommonTestBridge
```

Evidence:

| item | evidence |
|---|---|
| source involution bridge record | `ConnesWeilRH/Source/Objects.lean:36-41` |
| CCM24 common-test bridge record | `ConnesWeilRH/Source/Objects.lean:80-96` |
| CC20 common-test bridge record | `ConnesWeilRH/Source/Objects.lean:126-136` |
| source projection helpers | `ConnesWeilRH/Source/ObjectDerivations.lean:52-88` |
| route-facing projection helpers | `ConnesWeilRH/Route/RouteTheorem.lean:139-180` |

Do not start with:

```text
theorem final_rh : _root_.RiemannHypothesis
```

until the certificate constructors above exist without red assumptions. Adding
that theorem early would only hide the same conditional inputs under another
name.

## Completion Gate

This ledger can be closed only when the repository has evidence for all of the
following:

| requirement | required evidence |
|---|---|
| no `RouteCertificate` parameter in the final public theorem | Lean theorem statement for `_root_.RiemannHypothesis` with no source-package or certificate parameter |
| no undisclosed source-object assumptions | source-object fields are concrete definitions, accepted imports, or proved Lean theorems |
| all red rows discharged | accepted-source decision records or Lean theorem/axiom audits for CCM24, CCM25, CC20, sign/defect, restricted-to-full, final sign, and RH definition |
| route build passes | `lake build ConnesWeilRH` |
| final axiom audit passes | `#print axioms` shows only approved kernel/Mathlib foundations and explicitly accepted imports |

Until then, the correct public status remains:

```text
source-conditional route evidence, not an unconditional RH proof
```
