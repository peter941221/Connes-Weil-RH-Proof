# Source Object Theorem Discharge Ledger

Status: discharge ledger for the source-object definition theorem contract.

This ledger checks the first formal gate:

```text
SourceDefinitionSpineContract(S,I,lambda,g)
```

It does not discharge the gate. It records the evidence that a later source
import or Lean theorem must supply before the route may treat compact symbolic
records as source evidence.

## Result

Good result:

```text
The source-object definition gate now has a theorem-by-theorem discharge
ledger.
```

Bad result for final certification:

```text
No row below is yet discharged by a Lean theorem or by an accepted imported
source theorem with audited hypotheses.
```

This file is the next layer after:

```text
docs/proofs/source-object-definition-theorem-contract.md
```

It changes the question from:

```text
what theorem targets are needed?
```

to:

```text
what evidence would make each theorem target acceptable?
```

## Evidence Scale

| status | meaning | enough for final certificate? |
|---|---|---:|
| proof-package evidence | repository proof package names the route and source anchors | no |
| import-ready target | exact theorem shape and acceptance conditions are written | no |
| accepted source import | external theorem or source theorem proves the target with audited hypotheses | yes |
| Lean theorem | Lean proves the target and axiom audit matches the allowed source boundary | yes |

The current rows reach the first two statuses only.

## Contract Dependency Graph

```text
SourceObjectPackage(S,I,lambda,g)
        |
        +-- SourceCommonTestAndConvolution(g,F_g)
        |
        +-- SourceRouteTupleFixed(S,I,lambda,g)
        |
        +-- SourceWindowControlsRestrictedRoute(S,I,lambda,g)
        |
        +-- SourceCCM25WeilObjects(lambda,g,F_g)
        |
        +-- SourceCC20TraceObjects(S,I,lambda,g,F_g)
        |
        +-- SourceCC20RHExitObjects(g,F_g)
        |
        +-- SourceObjectPackageDerivesCompactRecords(S,I,lambda,g)
```

The graph has one ownership rule:

```text
the compact records are projections from SourceObjectPackage;
they are not independent source evidence.
```

## Row 1. SourceCommonTestAndConvolution

Target:

```text
SourceCommonTestAndConvolution(g,F_g)
```

Acceptance evidence:

| component | required source evidence |
|---|---|
| common test | one source test object `g` maps to CCM24 support, CCM25 `QW`, CC20 trace, and CC20 Mellin use |
| convolution square | one source equality `F_g = g^* * g` feeds finite primes, trace read-off, and Mellin vanishing |
| half-density convention | CCM25 and CC20 use the same normalization of the test |

Current repository evidence:

```text
docs/proofs/source-test-convolution-compatibility.md
docs/proofs/source-common-test-tuple-theorem-contract.md
docs/proofs/source-object-definition-spine-discharge.md
docs/proofs/source-object-definition-theorem-contract.md
```

Discharge requirement:

```text
import or prove a theorem that constructs CommonTestObject(g,F_g) and proves
that every CCM24, CCM25, and CC20 leg consumes that same object.
```

Reject:

```text
separate fields named ccm24Test, ccm25Test, cc20TraceTest, and cc20MellinTest
with no equality or transport theorem tying them to one source test.
```

Current status:

```text
import-ready target; not discharged.
```

## Row 2. SourceRouteTupleFixed

Target:

```text
SourceRouteTupleFixed(S,I,lambda,g)
```

Acceptance evidence:

| component | required source evidence |
|---|---|
| fixed place set | CCM24, trace, finite-prime visibility, and route certificates use the same `S` |
| fixed window | CCM24 support window and downstream restricted route use the same `I` |
| fixed restriction parameter | `lambda` is shared by the window containment and restricted `QW_lambda` leg |
| fixed test | the tuple uses the same `g` as Row 1 |

Current repository evidence:

```text
docs/proofs/source-object-definition-spine-discharge.md
docs/proofs/source-common-test-tuple-theorem-contract.md
formalization/source-object-interface-plan.md
docs/audits/formal-gate-spine-consistency-audit.md
```

Discharge requirement:

```text
import or prove projection equalities:
  ccm24Tuple_eq_sourceTuple
  ccm25Tuple_eq_sourceTuple
  cc20TraceTuple_eq_sourceTuple
  cc20ExitTuple_eq_sourceTuple.
```

Reject:

```text
constructing SemilocalModelSymbols, WeilFormSymbols, ArchimedeanTraceSymbols,
and FiniteVanishingCriterionPackage from separate tuple parameters.
```

Current status:

```text
import-ready target; not discharged.
```

## Row 3. SourceWindowControlsRestrictedRoute

Target:

```text
SourceWindowControlsRestrictedRoute(S,I,lambda,g)
```

Acceptance evidence:

| component | required source evidence |
|---|---|
| source support | `supp(g) subset I` in the CCM24 source model |
| Fourier support | Fourier support of `g` stays in the same `I` |
| convolution transport | `F_g=g^* * g` is transported through the same window |
| lambda containment | `I subset [lambda^(-1),lambda]` |
| downstream control | the same `I` controls `QW_lambda`, finite-prime visibility, and Cdef exhaustion |

Current repository evidence:

```text
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
docs/proofs/ccm25-restricted-qwlambda-window-discharge.md
docs/proofs/source-object-definition-spine-discharge.md
```

Discharge requirement:

```text
import or prove the window-control projections:
  ccm24Window_controls_qwLambda
  ccm24Window_controls_finitePrimeVisibility
  ccm24Window_controls_cdef.
```

Reject:

```text
lambdaCompatible : Prop
```

when it hides support containment, Fourier containment, convolution transport,
and downstream restricted-route ownership.

Current status:

```text
proof-package evidence; not discharged.
```

## Row 4. SourceCCM25WeilObjects

Target:

```text
SourceCCM25WeilObjects(lambda,g,F_g)
```

Acceptance evidence:

| component | required source evidence |
|---|---|
| global form | source `QW` and `Psi` definitions with `QW(g,g)=Psi(F_g)` |
| restricted form | source `QW_lambda` formula using the same `lambda` and window |
| finite primes | source prime-power support, restricted cut, `Lambda(n)`, pairing, and pointwise atom equality |
| pole | pole functional and restricted pole pairing under the same convention |
| sign | finite-prime, archimedean, and pole signs feed the final sign theorem |

Current repository evidence:

```text
docs/proofs/ccm25-qw-psi-definition-sign-discharge.md
docs/proofs/ccm25-restricted-qwlambda-window-discharge.md
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/final-sign-bridge-theorem-contract.md
```

Discharge requirement:

```text
import or prove that SourceObjectPackage projects:
  CCM25FinitePrimeNormalizationContract(lambda,g)
  FinalSignBridgeContract(g).
```

Reject:

```text
WeilFormSymbols
```

as primitive evidence when `QW`, finite-prime support, pole terms, or signs do
not project from the source package.

Current status:

```text
import-ready target; not discharged.
```

## Row 5. SourceCC20TraceObjects

Target:

```text
SourceCC20TraceObjects(S,I,lambda,g,F_g)
```

Acceptance evidence:

| component | required source evidence |
|---|---|
| trace test | CC20 trace object uses the common source test and `F_g` |
| operator identity | the positive trace operator is the one read later |
| Hilbert-Schmidt | the smoothing gate holds before trace-class is used |
| trace-class square | `A^*A` is trace-class before positivity |
| cyclicity ledger | every cyclic trace move has its own legality witness |
| read-off order | support-square trace and no-defect trace come after legality |

Current repository evidence:

```text
docs/proofs/cc20-trace-object-normalization-discharge.md
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
```

Discharge requirement:

```text
import or prove that SourceObjectPackage projects
CC20AnalyticTraceLegalityContract(S,I,lambda,g).
```

Reject:

```text
trace_eq_qw : Prop
```

as a standalone field with no operator identity, Hilbert-Schmidt, trace-class,
and cyclicity inputs.

Current status:

```text
import-ready target; not discharged.
```

## Row 6. SourceCC20RHExitObjects

Target:

```text
SourceCC20RHExitObjects(g,F_g)
```

Acceptance evidence:

| component | required source evidence |
|---|---|
| finite set | source finite set is exactly `F={0,1/2,1}` |
| Mellin vanishing | route triple vanishing becomes CC20 Mellin vanishing on that finite set |
| sign bridge | route `QW(g,g)>=0` becomes the CC20 nonpositivity input only through `QW(g,g)=-sum_v W_v(F_g)` |
| Proposition C.1 | the finite-vanishing criterion consumes the source zero predicate |
| Mathlib transport | source RH maps to `_root_.RiemannHypothesis` through zeta, zero, exclusion, and line bridges |

Current repository evidence:

```text
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/rh-definition-bridge-theorem-contract.md
```

Discharge requirement:

```text
import or prove that SourceObjectPackage projects:
  FinalSignBridgeContract(g)
  RHDefinitionBridgeContract
  the CC20 Proposition C.1 source theorem with the exact finite set.
```

Reject:

```text
criterion : tripleVanishing -> fullWeilPositivity -> RH
```

unless the sign bridge, finite set, source zero predicate, and Mathlib RH
bridge remain visible.

Current status:

```text
import-ready target; not discharged.
```

## Row 7. SourceObjectPackageDerivesCompactRecords

Target:

```text
SourceObjectPackageDerivesCompactRecords(S,I,lambda,g)
```

Acceptance evidence:

| projection | required source evidence |
|---|---|
| `toSemilocalModelSymbols` | derives CCM24 compact statements from the semilocal source package |
| `toWeilFormSymbols` | derives CCM25 compact statements from the Weil source package |
| `toArchimedeanTraceSymbols` | derives CC20 compact trace statements from the trace source package |
| `toFiniteVanishingCriterionPackage` | derives the finite-vanishing exit from the CC20 RH-exit source package |

Current repository evidence:

```text
docs/proofs/source-object-derived-compact-records.md
formalization/source-object-interface-plan.md
formalization/source-object-interface-workplan.md
```

Discharge requirement:

```text
import or prove projection theorems from SourceObjectPackage to each compact
record, then show the final route consumes only those projections.
```

Reject:

```text
direct constructors for compact records in route modules.
```

Current status:

```text
proof-package evidence; not discharged.
```

## Combined Acceptance Test

The source-object definition gate can count as discharged only when all seven
rows have accepted source imports or Lean theorems.

The accepted package must prove:

```text
SourceDefinitionSpineContract(S,I,lambda,g)
  ->
SourceDefinitionSpine(S,I,lambda,g)
```

and must show that the current compact route-facing records are projections:

```text
SourceObjectPackage
  -> SemilocalModelSymbols
  -> WeilFormSymbols
  -> ArchimedeanTraceSymbols
  -> FiniteVanishingCriterionPackage.
```

The audit must reject any proof that supplies:

```text
objectsCompatible : Prop
allGood : Prop
criterion : Prop
fullWeilPositivity : Prop
```

as a replacement for the named rows above.

## Current Judgment

| question | answer |
|---|---|
| Does this ledger prove any analytic source theorem? | no |
| Does it identify the exact source-object discharge rows? | yes |
| Does it preserve one `g`, one `F_g`, and one `(S,I,lambda)` tuple? | yes |
| Does it keep trace, finite-prime, sign, and RH-definition contracts visible? | yes |
| Can the source-object gate be marked discharged now? | no |

The next proof move is to attack Row 1 and Row 2 first. They are the ownership
base: without a common test and fixed tuple, the later trace, finite-prime,
sign, and RH-definition theorems can still apply to mismatched objects.
