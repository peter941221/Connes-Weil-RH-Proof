# Source Object Interface Plan

Status: documentation plan for the next Lean interface pass.

This file translates the source-object replacement batch into Lean-facing
interface work. It does not edit Lean code. It records the target shape for the
next `.lean` pass so the route does not collapse the new source-object bridges
back into opaque propositions.

## Boundary

The current committed Lean scaffold has four compact symbolic records:

```text
SemilocalModelSymbols
WeilFormSymbols
ArchimedeanTraceSymbols
FiniteVanishingCriterionPackage
```

These records let the route compose. They do not define CCM24 semilocal
objects, CCM25 Weil forms, CC20 trace objects, or the CC20 RH exit.

The source-object replacement batch now supplies the intended expanded shape:

```text
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md
docs/proofs/cc20-trace-object-normalization-discharge.md
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
docs/audits/source-object-replacement-consistency-audit.md
docs/audits/formal-gate-spine-consistency-audit.md
docs/proofs/source-object-definition-theorem-contract.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/rh-definition-bridge-theorem-contract.md
```

The next Lean interface pass should encode the expanded package first, then
derive the compact records from it.

## Target Dependency Shape

```text
SourceObjectPackage
  |
  +-- CommonTestObject
  |     |
  |     +-- one source test g
  |     +-- source convolution square F_g=g^* * g
  |
  +-- CCM24SemilocalObjectPackage
  |     |
  |     +-- source place set S
  |     +-- source support window I
  |     +-- canonical coordinate V_S=M_S U_S
  |     +-- support/Fourier/convolution transport
  |     +-- bounded comparison and fixed-window Sonin exhaustion
  |
  +-- CCM25WeilObjectPackage
  |     |
  |     +-- QW and Psi source definitions
  |     +-- QW_lambda source formula
  |     +-- source prime-power index support
  |     +-- Lambda(n) and <g|T(n)g>
  |     +-- pole and sign normalization
  |
  +-- CC20TraceObjectPackage
  |     |
  |     +-- source trace test
  |     +-- Hilbert-Schmidt gate
  |     +-- trace-class and cyclicity template
  |     +-- positive trace Tr(A^*A)
  |     +-- support-square and no-defect trace read-off
  |     +-- Mellin and sign normalizations
  |
  +-- CC20RHExitObjectPackage
        |
        +-- F={0,1/2,1}
        +-- finite-set admissibility
        +-- route triple vanishing as Mellin vanishing
        +-- QW >= 0 as CC20 nonpositivity through the sign bridge
        +-- Proposition C.1
        +-- source RH to Mathlib RH
```

The compact records should become derived views:

```text
SourceObjectPackage -> SemilocalModelSymbols
SourceObjectPackage -> WeilFormSymbols
SourceObjectPackage -> ArchimedeanTraceSymbols
SourceObjectPackage -> FiniteVanishingCriterionPackage
```

The derivation package is:

```text
docs/proofs/source-object-derived-compact-records.md
```

It gives the proof-package-level specification for the projection theorems that
the next Lean interface pass should implement.

The source-object definition theorem contract fixes the formal/import targets
for the package itself:

```text
docs/proofs/source-object-definition-theorem-contract.md
```

The next Lean interface pass should encode those targets before it treats the
compact records as source-backed evidence.

Before editing Lean, use this risk audit:

```text
formalization/source-object-interface-risk-audit.md
```

It lists the interface shapes that must be blocked, including route-owned
source objects, opaque bundled `Prop` fields, sum-level finite-prime
normalization, trace read-off before trace legality, and RH-name drift.

Also use this formal-gate spine audit:

```text
docs/audits/formal-gate-spine-consistency-audit.md
```

It fixes the order in which the source-definition, trace-legality,
finite-prime, sign, and RH-definition bridges should be consumed.

Use this workplan for the file-level implementation order:

```text
formalization/source-object-interface-workplan.md
```

It specifies the future `Objects.lean` and `ObjectDerivations.lean` split,
build order, grep gates, axiom audit, and rollback plan.

## First Lean Pass Without Analytic Proofs

The first code pass should introduce records and projection theorems only. It
should not attempt to formalize the analytic source proofs.

| step | target | reason |
|---|---|---|
| 1 | define `CommonTestObject` | fixes one `g` and one `F_g` before CCM24, CCM25, and CC20 consume it |
| 2 | define `CCM24SemilocalObjectPackage` | prevents window and fixed-`S` drift before restricted read-off |
| 3 | define `CCM25WeilObjectPackage` | makes finite-prime index, weight, pairing, pole, and sign data visible |
| 4 | define `CC20TraceObjectPackage` | forces trace-class and cyclicity before positive trace and read-off |
| 5 | define `CC20RHExitObjectPackage` | separates Proposition C.1 from the Mathlib RH definition bridge |
| 6 | define `SourceObjectPackage` | bundles the five packages with cross-package compatibility fields |
| 7 | derive compact records | keeps existing route modules stable while tightening the source boundary |
| 8 | rebuild `ConnesWeilRH` | verifies the route still composes from the expanded source object boundary |

This pass may use `Prop` fields for source theorem outputs. It should not use a
single opaque `criterion` or `fullWeilPositivity` field where the replacement
batch requires named bridge components.

## Required Cross-Package Fields

The bundle must expose these compatibility fields.

| field | role |
|---|---|
| `ccm24Test_eq_commonTest` | CCM24 support test is the common source test |
| `ccm25Test_eq_commonTest` | CCM25 Weil test is the common source test |
| `cc20TraceTest_eq_commonTest` | CC20 trace test is the common source test |
| `cc20MellinTest_eq_commonTest` | CC20 Mellin test uses the same half-density convention |
| `convolutionSquare_eq_Fg` | finite-prime support and trace read-off use the same `F_g` |
| `ccm24Window_controls_qwLambda` | restricted `QW_lambda` uses the CCM24 source window |
| `ccm24Window_controls_cdef` | Cdef exhaustion uses the same fixed window |
| `finitePrimeSupport_matches_window` | visible prime-power atoms fit the restricted lambda cut |
| `qW_sign_bridge` | `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)` and `QW(g,g)>=0 -> sum_v W_v(g * bar(g)^sharp)<=0` are derived from the final sign theorem contract |
| `sourceRH_to_mathlibRH` | CC20 source RH implies Mathlib `_root_.RiemannHypothesis` through the RH definition theorem contract |

These fields should be named. A later axiom audit or source-import audit can
then inspect each bridge directly.

## Compact Record Derivations

### SemilocalModelSymbols

Derive:

```text
SemilocalModelSymbols.CanonicalSemilocalModelStatement
SemilocalModelSymbols.SupportTransportStatement
SemilocalModelSymbols.BoundedComparisonStatement
SemilocalModelSymbols.SoninComparisonStatement
```

from:

```text
CCM24SemilocalObjectPackage
```

Do not allow `canonicalHilbertModel`, `supportInWindow`,
`boundedComparisonMap`, or `soninSpaceComparison` to remain final evidence
without the source package behind them.

### WeilFormSymbols

Derive:

```text
WeilFormSymbols.QWDefinitionStatement
WeilFormSymbols.PsiSignStatement
WeilFormSymbols.QWLambdaFormulaStatement
WeilFormSymbols.FinitePrimeNormalizationStatement
WeilFormSymbols.PoleNormalizationStatement
```

from:

```text
CCM25WeilObjectPackage
CommonTestObject
CCM24SemilocalObjectPackage
```

The finite-prime derivation must keep pointwise source terms:

```text
finitePrimeTerm n F_g = Lambda(n)<g|T(n)g>
```

for every source prime-power index `n`.

The CCM25 finite-prime normalization theorem contract fixes the formal/import
targets behind those terms:

```text
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
```

The later Lean interface should derive compact fields such as
`globalPrimeIndexSet`, `restrictedPrimeIndexSet`, `finitePrimeTerm`,
`vonMangoldtWeight`, and `primePowerPairing` from that contract rather than
accepting them as primitive source evidence.

The final sign derivation must consume:

```text
docs/proofs/final-sign-bridge-theorem-contract.md
```

before any final-exit package treats route `QW(g,g) >= 0` as the CC20
nonpositivity hypothesis.

### ArchimedeanTraceSymbols

Derive:

```text
ArchimedeanTraceSymbols.TraceSquareStatement
ArchimedeanTraceSymbols.TraceClassTemplateStatement
ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
```

from:

```text
CC20TraceObjectPackage
CommonTestObject
CCM25WeilObjectPackage
```

The trace package must keep:

```text
Hilbert-Schmidt gate
  -> trace-class and cyclicity
  -> positive trace Tr(A^*A)
  -> support-square trace
  -> no-defect source trace
```

as named stages.

The CC20 analytic trace-legality theorem contract fixes the formal/import
targets behind those stages:

```text
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
```

The later Lean interface should derive compact fields such as `traceClass`,
`cyclicLegal`, and `positiveTrace` from that contract rather than accepting
them as primitive source evidence.

### FiniteVanishingCriterionPackage

Derive:

```text
FiniteVanishingCriterionPackage.finiteSetAdmissible
FiniteVanishingCriterionPackage.criterion
```

from:

```text
CC20RHExitObjectPackage
CC20TraceObjectPackage
CCM25WeilObjectPackage
```

The derivation must expose:

```text
F={0,1/2,1}
route triple vanishing = CC20 Mellin vanishing on F
QW(g,g) >= 0 = CC20 nonpositivity through sign bridge
CC20 Proposition C.1
source RH -> Mathlib RH
```

The Mathlib RH leg must consume:

```text
docs/proofs/rh-definition-bridge-theorem-contract.md
```

before any final route theorem treats a source theorem named `RH` as
`_root_.RiemannHypothesis`.

## Module Placement

Use new modules under the source layer, not route modules:

```text
ConnesWeilRH/Source/Objects.lean
ConnesWeilRH/Source/ObjectDerivations.lean
```

Reason:

```text
source-object packages are source-boundary data;
route modules should consume derived interfaces, not define source objects.
```

Suggested import direction:

```text
ConnesWeilRH.Basic
      |
      v
ConnesWeilRH.Source.Objects
      |
      v
ConnesWeilRH.Source.ObjectDerivations
      |
      v
ConnesWeilRH.Source.CCM24 / CCM25 / CC20
      |
      v
ConnesWeilRH.Route.*
```

If this creates import cycles with current source modules, keep
`Objects.lean` independent and let `CCM24.lean`, `CCM25.lean`, and `CC20.lean`
import the derivation module only after the compact records remain in
`Basic.lean`.

## Build And Audit Gate

A successful interface pass must run:

```text
lake build ConnesWeilRH
```

and then re-run:

```text
#print axioms ConnesWeilRH.Route.final_connes_weil_rh
```

Expected result after a pure interface pass:

```text
no new project-local axioms outside approved source interfaces.
```

If the axiom list grows, the pass failed the interface hygiene goal.

## Non-Goals

Do not do these in the first interface pass:

| non-goal | reason |
|---|---|
| prove CCM24 semilocal analysis | source theorem work, not interface work |
| prove CCM25 explicit formulas | source theorem work, not interface work |
| prove CC20 trace-class theorem | source theorem work, not interface work |
| prove Proposition C.1 | source theorem work, not interface work |
| replace Mathlib RH | final theorem already targets `_root_.RiemannHypothesis` |
| rewrite route modules broadly | route composition already builds from compact interfaces |

## Current Judgment

| question | answer |
|---|---|
| Is Lean code changed by this plan? | no |
| Is the next Lean pass now scoped? | yes |
| Should compact records remain available? | yes, as derived views |
| Should compact records remain final evidence? | no |
| Does this prove RH? | no |

The next implementation milestone is a small Lean interface pass that adds the
expanded source-object package and derives the existing compact records from it.
