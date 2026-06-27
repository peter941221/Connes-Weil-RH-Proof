# Source Object Interface Workplan

Status: executable workplan for the next Lean interface pass.

This workplan converts:

```text
formalization/source-object-interface-plan.md
formalization/source-object-interface-risk-audit.md
docs/proofs/source-object-derived-compact-records.md
```

into a file-level implementation sequence. It does not edit Lean code. It sets
the order for the future Lean pass that makes source-object packages visible
while keeping the current route modules stable.

## Goal

Implement a Lean-visible source-object boundary:

```text
expanded source-object packages
  |
  v
derived compact records
  |
  v
existing route modules
```

The pass should not prove CCM24, CCM25, or CC20 analytic content. It should
make the existing source assumptions more structured and harder to misuse.

## Files To Add Later

| file | purpose |
|---|---|
| `ConnesWeilRH/Source/Objects.lean` | define expanded source-object package records |
| `ConnesWeilRH/Source/ObjectDerivations.lean` | define projections from expanded packages to compact records and prove compact statements |

Do not add source-object records under:

```text
ConnesWeilRH/Route/
```

Route modules should consume source interfaces. They should not own source
objects.

## Phase 0. Preflight

Before editing Lean, verify the working tree:

```text
git status --short --branch
rg -n "sorry|admit|axiom|constant|opaque|unsafe" ConnesWeilRH -g "*.lean"
```

Expected result:

```text
no unrelated unstaged Lean changes
no unapproved proof debt in route modules
```

Read these files first:

```text
formalization/source-object-interface-plan.md
formalization/source-object-interface-risk-audit.md
docs/proofs/source-object-derived-compact-records.md
docs/audits/source-object-replacement-consistency-audit.md
```

## Phase 1. Add Objects.lean

Create:

```text
ConnesWeilRH/Source/Objects.lean
```

Import:

```text
import ConnesWeilRH.Basic
```

Define these records:

```text
CommonTestObject
CCM24SemilocalObjectPackage
CCM25WeilObjectPackage
CC20TraceObjectPackage
CC20RHExitObjectPackage
SourceObjectPackage
```

Required fields:

| record | required fields |
|---|---|
| `CommonTestObject` | common test, convolution square `F_g`, and source convolution/involution bridge |
| `CCM24SemilocalObjectPackage` | place set, support window, source test leg, canonical model, support/Fourier transport, convolution transport, bounded comparison, Sonin exhaustion |
| `CCM25WeilObjectPackage` | `QW`, `Psi`, `QW_lambda`, source prime-power support, lambda cut, `Lambda(n)`, `<g|T(n)g>`, pointwise finite-prime terms, pole, archimedean sign |
| `CC20TraceObjectPackage` | trace test, Hilbert-Schmidt gate, trace-class, cyclicity, positive trace, support-square trace, no-defect trace, Mellin bridge, sign bridge |
| `CC20RHExitObjectPackage` | `F={0,1/2,1}`, finite-set admissibility, triple-vanishing-to-Mellin bridge, CC20 inequality bridge, Proposition C.1, source-RH-to-Mathlib bridge |
| `SourceObjectPackage` | the five packages plus cross-package compatibility fields |

Blocking rule:

```text
do not add fields named allGood, complete, exitWorks, or everything.
```

Reason:

```text
those names hide the proof obligations this pass is supposed to expose.
```

## Phase 2. Add ObjectDerivations.lean

Create:

```text
ConnesWeilRH/Source/ObjectDerivations.lean
```

Import:

```text
import ConnesWeilRH.Source.Objects
```

Define projections:

```text
SourceObjectPackage.toSemilocalModelSymbols
SourceObjectPackage.toWeilFormSymbols
SourceObjectPackage.toArchimedeanTraceSymbols
SourceObjectPackage.toFiniteVanishingCriterionPackage
```

Prove compact statements:

```text
SourceObjectPackage.provesCanonicalSemilocalModelStatement
SourceObjectPackage.provesSupportTransportStatement
SourceObjectPackage.provesBoundedComparisonStatement
SourceObjectPackage.provesSoninComparisonStatement

SourceObjectPackage.provesQWDefinitionStatement
SourceObjectPackage.provesPsiSignStatement
SourceObjectPackage.provesQWLambdaFormulaStatement
SourceObjectPackage.provesFinitePrimeNormalizationStatement
SourceObjectPackage.provesPoleNormalizationStatement

SourceObjectPackage.provesTraceSquareStatement
SourceObjectPackage.provesTraceClassTemplateStatement
SourceObjectPackage.provesMellinHalfDensityConventionStatement
SourceObjectPackage.provesSignsAndNormalizationsStatement

SourceObjectPackage.provesFiniteSetAdmissible
SourceObjectPackage.provesFiniteVanishingCriterion
```

Theorems should be projections or short compositions. If a proof needs deep
analysis, the record fields are too weak or the theorem belongs to a later
source-discharge phase.

## Phase 3. Wire Source Interfaces

Update source-interface modules only after `ObjectDerivations.lean` builds:

```text
ConnesWeilRH/Source/CCM24.lean
ConnesWeilRH/Source/CCM25.lean
ConnesWeilRH/Source/CC20.lean
```

Safe first wiring:

```text
keep existing compact interface fields;
add optional expanded package fields only if they derive the compact fields;
avoid breaking route imports.
```

Do not rewrite route modules in this phase unless the build forces a minimal
import fix.

## Phase 4. Build

Build the smallest targets first:

```text
lake build ConnesWeilRH.Source.Objects
lake build ConnesWeilRH.Source.ObjectDerivations
lake build ConnesWeilRH.Source.CCM24
lake build ConnesWeilRH.Source.CCM25
lake build ConnesWeilRH.Source.CC20
lake build ConnesWeilRH
```

If a segment fails, fix the first failing module. Do not patch downstream
route modules to silence a source-interface error.

## Phase 5. Grep Gates

Run:

```text
rg -n "allGood|everything|complete|exitWorks" ConnesWeilRH/Source -g "*.lean"
```

Expected:

```text
no matches.
```

Run:

```text
rg -n "structure .*Source|def .*Source|theorem .*Source" ConnesWeilRH/Route -g "*.lean"
```

Expected:

```text
no new route-owned source-object definitions.
```

Run:

```text
rg -n "sorry|admit|axiom|constant|opaque|unsafe" ConnesWeilRH -g "*.lean"
```

Expected:

```text
no new unapproved proof debt.
```

## Phase 6. Axiom Audit

Create a temporary file named:

```text
connes_axiom_audit.lean
```

with:

```text
import ConnesWeilRH
#print axioms ConnesWeilRH.Route.final_connes_weil_rh
```

Run:

```text
lake env lean connes_axiom_audit.lean
```

Expected after an interface-only pass:

```text
no new project-local axioms outside approved source-interface contracts.
```

Remove the temporary audit file unless it is intentionally committed as a
public audit artifact.

## Review Checklist

Before committing the Lean interface pass:

| check | required result |
|---|---|
| `Objects.lean` defines expanded packages | yes |
| `ObjectDerivations.lean` derives compact records | yes |
| route modules define no source objects | yes |
| finite-prime normalization remains pointwise | yes |
| trace legality precedes read-off | yes |
| final sign bridge is named | yes |
| source RH to Mathlib RH bridge is named | yes |
| `lake build ConnesWeilRH` passes | yes |
| axiom audit remains clean | yes |

## Rollback Plan

If the interface pass introduces route churn:

```text
revert route-module edits first;
keep Objects.lean and ObjectDerivations.lean isolated;
rebuild source modules;
only reconnect route modules after compact records still derive.
```

If the axiom audit grows:

```text
identify the new axiom;
move it into an approved source-interface record only if it is a genuine
source theorem contract;
otherwise remove it.
```

## Done Criteria

The Lean interface pass is complete when:

```text
expanded source-object packages exist;
compact records derive from them;
route theorem still builds;
axiom audit stays clean;
no source objects live in route modules.
```

This workplan does not prove RH. It makes the next Lean implementation step
small, auditable, and aligned with the source-object proof packages.
