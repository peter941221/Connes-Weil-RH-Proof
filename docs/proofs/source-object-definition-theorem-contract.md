# Source Object Definition Theorem Contract

Status: theorem contract for the source-object definition gate.

This file converts:

```text
docs/proofs/source-object-definition-spine-discharge.md
```

from a proof-package spine into precise theorem targets for a future Lean pass
or accepted source import. It does not define the analytic CCM24, CCM25, or
CC20 objects. It fixes the source-object package that must exist before compact
route records can count as source evidence.

## Evidence Lock

| item | evidence |
|---|---|
| source-object definition ledger | `docs/audits/source-object-definition-ledger.md` |
| source-definition spine package | `docs/proofs/source-object-definition-spine-discharge.md` |
| common test and convolution square | `docs/proofs/source-test-convolution-compatibility.md` |
| CCM24 source object package | `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` |
| CCM25 source object packages | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` |
| CC20 trace legality contract | `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` |
| final sign contract | `docs/proofs/final-sign-bridge-theorem-contract.md` |
| RH definition contract | `docs/proofs/rh-definition-bridge-theorem-contract.md` |
| source-object interface plan | `formalization/source-object-interface-plan.md` |
| source-object interface risk audit | `formalization/source-object-interface-risk-audit.md` |

This contract is the top-level package target. The other contracts can become
fields or theorem projections from this package.

## Boundary

This contract gives a stronger target than the current proof package:

```text
proof-package spine
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

The final RH route cannot treat this contract as discharge. A later phase must
replace each target below with a Lean theorem or an accepted imported theorem.

## Top-Level Object

The future source boundary must expose one package:

```text
SourceObjectPackage(S,I,lambda,g)
```

with source-owned subpackages:

```text
CommonTestObject(g,F_g)
CCM24SemilocalObjectPackage(S,I,lambda,g)
CCM25WeilObjectPackage(lambda,g,F_g)
CC20TraceObjectPackage(S,I,lambda,g,F_g)
CC20RHExitObjectPackage(g,F_g)
RHDefinitionBridgePackage
```

The compact current records must become projections:

```text
SourceObjectPackage -> SemilocalModelSymbols
SourceObjectPackage -> WeilFormSymbols
SourceObjectPackage -> ArchimedeanTraceSymbols
SourceObjectPackage -> FiniteVanishingCriterionPackage
```

Blocked shortcut:

```text
objectsCompatible : Prop
```

as the only source-object evidence.

## Contract Theorem 1. Common Test And Convolution Square

Target:

```text
SourceCommonTestAndConvolution:
  CommonTestObject(g,F_g)
  and F_g = g^* * g
  and the same g and F_g feed CCM24, CCM25, CC20 trace, CC20 Mellin, and the
  final sign/RH exit.
```

Meaning:

The route must not allocate separate tests for support transport, finite-prime
read-off, trace legality, Mellin vanishing, and final sign bridge.

Evidence used:

```text
docs/proofs/source-test-convolution-compatibility.md
docs/proofs/source-object-definition-spine-discharge.md:84-169
docs/audits/formal-gate-spine-consistency-audit.md:67-94
```

Blocked shortcut:

```text
test : TestFunction
```

copied independently into CCM24, CCM25, and CC20 fields.

## Contract Theorem 2. One Route Tuple

Target:

```text
SourceRouteTupleFixed:
  every source object consumed by the route is indexed by the same
  (S,I,lambda,g).
```

Required projections:

```text
ccm24Tuple_eq_sourceTuple
ccm25Tuple_eq_sourceTuple
cc20TraceTuple_eq_sourceTuple
cc20ExitTuple_eq_sourceTuple
```

Meaning:

The package must make tuple sharing visible. A later Lean interface can derive
compact records, but those records cannot choose new `S`, `I`, `lambda`, or
`g` values.

Evidence used:

```text
docs/proofs/source-object-definition-spine-discharge.md:84-118
formalization/source-object-interface-plan.md:151-169
```

Blocked shortcut:

```text
SemilocalModelSymbols
WeilFormSymbols
ArchimedeanTraceSymbols
```

constructed independently.

## Contract Theorem 3. CCM24 Window Owns The Restricted Route

Target:

```text
SourceWindowControlsRestrictedRoute:
  I is the CCM24 source support window,
  supp(g) subset I,
  Fourier support of g lies in I,
  convolution support of F_g is transported through I,
  I subset [lambda^(-1),lambda],
  and this same window controls QW_lambda, finite-prime visibility, and Cdef
  exhaustion.
```

Required projections:

```text
ccm24Window_controls_qwLambda
ccm24Window_controls_finitePrimeVisibility
ccm24Window_controls_cdef
```

Meaning:

The positive trace, restricted CCM25 form, finite-prime cut, and endpoint-strip
exhaustion must use the same source window.

Evidence used:

```text
docs/proofs/source-object-definition-spine-discharge.md:170-209
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
docs/proofs/ccm25-restricted-qwlambda-window-discharge.md
docs/audits/formal-gate-spine-consistency-audit.md:96-124
```

Blocked shortcut:

```text
lambdaCompatible : Prop
```

with no visible support-window chain.

## Contract Theorem 4. CCM25 Weil Objects Project From The Source Package

Target:

```text
SourceCCM25WeilObjects:
  QW, Psi, QW_lambda, global prime support, restricted prime support,
  Lambda(n), <g|T(n)g>, finite-prime term normalization, pole functional, and
  sign data are fields or theorem projections of SourceObjectPackage.
```

Required contract inclusions:

```text
CCM25FinitePrimeNormalizationContract(lambda,g)
FinalSignBridgeContract(g)
```

Meaning:

The route may use compact `WeilFormSymbols` only after deriving them from the
source package. It cannot supply an arbitrary `QW`, finite-prime support, or
sign bridge as route-local data.

Evidence used:

```text
docs/proofs/source-object-definition-spine-discharge.md:119-169
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/audits/source-object-definition-ledger.md:81-119
```

Blocked shortcut:

```text
WeilFormSymbols
```

as primitive final source evidence.

## Contract Theorem 5. CC20 Trace Objects Project From The Source Package

Target:

```text
SourceCC20TraceObjects:
  the CC20 trace test, Hilbert-Schmidt gate, trace-class square,
  cyclicity ledger, ordinary positive trace, support-square trace,
  no-defect trace, Mellin convention, and sign convention are fields or theorem
  projections of SourceObjectPackage.
```

Required contract inclusion:

```text
CC20AnalyticTraceLegalityContract(S,I,lambda,g)
```

Meaning:

Trace read-off must consume trace legality. A compact `positiveTrace` or
`sourceNoDefectTrace` field cannot stand alone.

Evidence used:

```text
docs/proofs/source-object-definition-spine-discharge.md:210-244
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
docs/proofs/cc20-trace-object-normalization-discharge.md
```

Blocked shortcut:

```text
trace_eq_qw : Prop
```

without operator identity, trace-class square, and per-move cyclicity inputs.

## Contract Theorem 6. CC20 RH Exit Projects From The Source Package

Target:

```text
SourceCC20RHExitObjects:
  F={0,1/2,1}, finite-set admissibility, route triple-vanishing-to-Mellin
  translation, final sign bridge consumption, Proposition C.1, source RH, and
  Mathlib RH transport are fields or theorem projections of SourceObjectPackage.
```

Required contract inclusions:

```text
FinalSignBridgeContract(g)
RHDefinitionBridgeContract
```

Meaning:

The final exit package must not bundle the CC20 criterion, sign bridge, and
Mathlib RH bridge into one opaque `criterion` field.

Evidence used:

```text
docs/proofs/source-object-definition-spine-discharge.md:245-283
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/rh-definition-bridge-theorem-contract.md
```

Blocked shortcut:

```text
criterion : input -> tripleVanishing -> fullWeilPositivity -> RH
```

with no named sign and Mathlib-definition bridges.

## Contract Theorem 7. Compact Records Are Derived Views

Target:

```text
SourceObjectPackageDerivesCompactRecords:
  SourceObjectPackage(S,I,lambda,g)
  -> SemilocalModelSymbols
  -> WeilFormSymbols
  -> ArchimedeanTraceSymbols
  -> FiniteVanishingCriterionPackage.
```

Required projection theorems:

```text
toSemilocalModelSymbols
toWeilFormSymbols
toArchimedeanTraceSymbols
toFiniteVanishingCriterionPackage
```

Meaning:

The compact records can stay as a stable route interface, but they must no
longer be primitive source evidence.

Evidence used:

```text
docs/proofs/source-object-derived-compact-records.md
formalization/source-object-interface-plan.md
formalization/source-object-interface-workplan.md
```

Blocked shortcut:

```text
construct compact records directly in Route modules.
```

## Combined Contract

The formal/import target for this gate is:

```text
SourceDefinitionSpineContract(S,I,lambda,g):
  SourceCommonTestAndConvolution(g,F_g)
  SourceRouteTupleFixed(S,I,lambda,g)
  SourceWindowControlsRestrictedRoute(S,I,lambda,g)
  SourceCCM25WeilObjects(lambda,g,F_g)
  SourceCC20TraceObjects(S,I,lambda,g,F_g)
  SourceCC20RHExitObjects(g,F_g)
  SourceObjectPackageDerivesCompactRecords(S,I,lambda,g)
```

Projection target:

```text
SourceDefinitionSpineContract(S,I,lambda,g)
  ->
SourceDefinitionSpine(S,I,lambda,g).
```

Route consumption target:

```text
SourceDefinitionSpineContract(S,I,lambda,g)
  ->
the route may derive the compact source records it currently consumes.
```

only through:

```text
one source object package
  -> common test and convolution square
  -> CCM24 source window
  -> CCM25 Weil objects
  -> CC20 trace objects
  -> CC20 RH exit objects
  -> Mathlib RH target
  -> compact record projections.
```

## Import Acceptance Checklist

A source import can discharge this contract only if it supplies these items:

| item | required evidence |
|---|---|
| common test | one `g` and one `F_g=g^* * g` |
| tuple | all packages use the same `(S,I,lambda,g)` |
| window | one CCM24 source window controls support, `QW_lambda`, finite primes, and Cdef |
| CCM25 objects | QW/Psi/QW_lambda, finite-prime, pole, and sign contracts project from the package |
| CC20 trace objects | trace-legality contract projects from the package |
| CC20 exit objects | finite set, Mellin vanishing, sign bridge, Proposition C.1, and RH bridge project from the package |
| compact projections | existing compact route records are derived, not primitive |
| module boundary | source objects live under the source-interface layer, not route modules |

If an import supplies only a single compatibility proposition, it fails this
contract.

## Lean Interface Consequence

A later Lean interface should define records matching:

```text
CommonTestObject
CCM24SemilocalObjectPackage
CCM25WeilObjectPackage
CC20TraceObjectPackage
CC20RHExitObjectPackage
SourceObjectPackage
```

and projection theorems matching:

```text
SourceObjectPackage.toSemilocalModelSymbols
SourceObjectPackage.toWeilFormSymbols
SourceObjectPackage.toArchimedeanTraceSymbols
SourceObjectPackage.toFiniteVanishingCriterionPackage
```

The first Lean pass may keep theorem bodies as source-interface assumptions.
It must still expose the names above so that `#print axioms` shows which
source-definition contracts the final route consumes.

## Current Judgment

| question | answer |
|---|---|
| Does this contract define CCM24, CCM25, or CC20 analytic objects? | no |
| Does it specify the theorem shape needed to discharge the source-definition gate? | yes |
| Does it force one `g` and one `F_g`? | yes |
| Does it force one `(S,I,lambda)` tuple? | yes |
| Does it force compact records to be derived views? | yes |
| Does it keep sign, trace, finite-prime, and RH-definition contracts visible? | yes |
| Can a later Lean/source-import pass use this as a checklist? | yes |

The source-definition gate is now stated as a theorem contract. The next work
is to commit this with the RH definition contract as the next signed milestone,
then prepare for the future Lean interface phase only after Peter reopens it.
