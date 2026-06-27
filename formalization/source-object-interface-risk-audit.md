# Source Object Interface Risk Audit

Status: pre-Lean risk audit for the source-object interface pass.

This audit lists the failure modes that would make a future Lean interface pass
look cleaner while weakening the proof. It pairs each risk with a concrete
blocking rule and an evidence check.

It governs the pass described in:

```text
formalization/source-object-interface-plan.md
formalization/source-object-interface-workplan.md
docs/proofs/source-object-derived-compact-records.md
docs/audits/formal-gate-spine-consistency-audit.md
```

## Result

Good result:

```text
The next Lean pass has a narrow safe path:
define expanded source-object packages,
derive compact records,
keep route modules stable,
and rerun build plus axiom audit.
```

Bad result if ignored:

```text
Lean can accept a cleaner interface that still hides the same source-object
gaps behind compact Prop fields.
```

## Risk Matrix

| risk | failure mode | blocking rule | evidence check |
|---|---|---|---|
| opaque source package | `SourceObjectPackage` has fields like `allGood : Prop` | every source bridge named in the plan must appear as a named field or theorem | grep for `allGood`, `complete`, `criterion`, `fullWeilPositivity` in new source-object modules |
| route-owned source objects | route modules define CCM24/CCM25/CC20 source objects | source objects live under `ConnesWeilRH/Source/` | new files under `ConnesWeilRH/Route/` must not define source-object records |
| compact records remain primitive | `SemilocalModelSymbols`, `WeilFormSymbols`, `ArchimedeanTraceSymbols`, or `FiniteVanishingCriterionPackage` are still supplied directly | compact records must be derived from expanded packages | look for constructors of compact records outside `ObjectDerivations.lean` and source-interface wiring |
| test drift | CCM24, CCM25, and CC20 packages each choose their own test type | `CommonTestObject` owns the source test and `F_g` | fields `ccm24Test_eq_commonTest`, `ccm25Test_eq_commonTest`, `cc20TraceTest_eq_commonTest`, and `cc20MellinTest_eq_commonTest` exist |
| window drift | `QW_lambda` and Cdef exhaustion use different windows | CCM24 source window controls both | fields `ccm24Window_controls_qwLambda` and `ccm24Window_controls_cdef` exist |
| finite-prime collapse | finite-prime normalization is only a sum equality | pointwise prime-power term equality must remain visible | theorem for `finitePrimeTerm n F_g = Lambda(n)<g|T(n)g>` exists |
| trace collapse | positive trace, support-square trace, and no-defect trace are conflated | trace stages remain named | fields for Hilbert-Schmidt, trace-class, cyclicity, positive trace, support-square trace, and no-defect read-off exist |
| sign collapse | `QW >= 0` is accepted as the CC20 inequality without sign theorem | sign bridge is a named theorem | field `qW_sign_bridge` exists and feeds RH exit |
| RH-name drift | CC20 source RH is treated as Mathlib RH by name | source-to-Mathlib bridge is explicit | field `sourceRH_to_mathlibRH` exists |
| axiom leak | interface pass adds project-local axioms | no new axioms outside source interfaces | rerun `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` |

## Blocking Rules

### Rule 1. Source Objects Stay In Source Modules

Allowed:

```text
ConnesWeilRH/Source/Objects.lean
ConnesWeilRH/Source/ObjectDerivations.lean
```

Not allowed:

```text
ConnesWeilRH/Route/Objects.lean
ConnesWeilRH/Route/SourceObjects.lean
```

Reason:

```text
source-object packages are source-boundary data.
route modules should consume source interfaces, not define them.
```

### Rule 2. Compact Records Are Derived Views

Allowed:

```text
def SourceObjectPackage.toWeilFormSymbols : WeilFormSymbols := ...

theorem SourceObjectPackage.provesFinitePrimeNormalization :
  WeilFormSymbols.FinitePrimeNormalizationStatement
    SourceObjectPackage.toWeilFormSymbols := ...
```

Not allowed:

```text
structure NewCCM25Interface where
  weilSymbols : WeilFormSymbols
  finitePrimeNormalization :
    WeilFormSymbols.FinitePrimeNormalizationStatement weilSymbols
```

without the expanded source-object package behind it.

Reason:

```text
that recreates the old compact boundary under a new name.
```

### Rule 3. Named Bridges Beat Bundled Prop Fields

Allowed:

```text
qW_sign_bridge :
  QW g g = -cc20WeilSum g

sourceRH_to_mathlibRH :
  SourceRH -> _root_.RiemannHypothesis
```

Not allowed:

```text
exitWorks : Prop
criterion : input -> input.tripleVanishing -> input.fullWeilPositivity -> RH
```

as the only final-exit evidence.

Reason:

```text
the proof must expose the sign and definition bridges for audit.
```

The proof-package target for the sign part is:

```text
docs/proofs/final-sign-bridge-spine-discharge.md
```

It requires `QW(g,g)=-sum_v W_v(F_g)` and the derived inequality direction as
separate theorem targets.

The stronger theorem-contract target is:

```text
docs/proofs/final-sign-bridge-theorem-contract.md
```

It requires common source test, source `Psi` sign expansion, archimedean sign
bridge, finite-prime sign ownership, source pole sign in the CC20 local sum,
`QW(g,g)=-sum_v W_v(F_g)`, and
`QW(g,g)>=0 -> sum_v W_v(F_g)<=0` to remain named theorem targets.

The proof-package target for the RH definition part is:

```text
docs/proofs/rh-definition-bridge-spine-discharge.md
```

It requires source zeta transport, zero transport, negative-even exclusion,
pole exclusion, and critical-line equivalence as separate theorem targets.

### Rule 4. Pointwise Finite-Prime Data Cannot Be Replaced By Sum Equality

Allowed:

```text
sourceFinitePrimeTerm_eq :
  forall n, SourcePrimePowerIndex n ->
    finitePrimeTerm n F_g = Lambda n * primePowerPairing n g g
```

Not allowed:

```text
restrictedFinitePrimeSumsEqual : Prop
```

as the only finite-prime theorem.

Reason:

```text
sum-level equality can hide wrong weights or wrong pairings by cancellation.
```

The proof-package target for this risk is:

```text
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md
```

It requires pointwise atom normalization before any global or restricted
finite-prime sum is used.

The stronger theorem-contract target is:

```text
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
```

It requires prime-power factorization, global source support, restricted
lambda-cut support, visibility before the cut, fixed-S visible-prime
admissibility, source `Lambda(n)`, source `<g|T(n)g>`, pointwise atom equality,
and finite-prime sign ownership to remain named theorem targets.

### Rule 5. Trace Legality Comes Before Trace Read-Off

Allowed chain:

```text
Hilbert-Schmidt gate
  -> trace-class
  -> cyclicity
  -> positive trace
  -> support-square trace
  -> no-defect trace
  -> Weil-form read-off
```

Not allowed:

```text
trace_eq_qw : Prop
```

without named trace-class and cyclicity inputs.

Reason:

```text
positivity and cyclic trace moves are valid only after trace legality.
```

The proof-package target for this risk is:

```text
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
```

It requires a per-move cyclicity witness ledger rather than a single
`cyclicLegal : Prop` permission.

The stronger theorem-contract target is:

```text
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
```

It requires operator identity, Hilbert-Schmidt, trace-class square,
ordinary-trace equality, per-move cyclicity, support-square read-off,
no-defect read-off, and bounded-comparison transport to remain named theorem
targets.

## Required Grep Gates

After a Lean interface pass, run:

```text
rg -n "allGood|everything|complete|opaque|axiom|admit|sorry" ConnesWeilRH -g "*.lean"
```

Expected result:

```text
no new route-layer proof debt or opaque source package fields.
```

Run:

```text
rg -n "structure .*Source|def .*Source|theorem .*Source" ConnesWeilRH/Route -g "*.lean"
```

Expected result:

```text
no route-owned source-object definitions.
```

Run:

```text
rg -n "FiniteVanishingCriterionPackage|SemilocalModelSymbols|WeilFormSymbols|ArchimedeanTraceSymbols" ConnesWeilRH/Source -g "*.lean"
```

Expected result:

```text
compact records appear in derivation modules or source-interface wiring,
not as final primitive evidence.
```

## Required Build Gate

Run from the WSL ext4 mirror:

```text
lake build ConnesWeilRH
```

Then run the axiom audit:

```text
lake env lean connes_axiom_audit.lean
```

where `connes_axiom_audit.lean` is a temporary axiom-audit file containing:

```text
import ConnesWeilRH
#print axioms ConnesWeilRH.Route.final_connes_weil_rh
```

Acceptable result after an interface-only pass:

```text
no new project-local axioms outside the approved source-interface boundary.
```

## Review Checklist

Before committing a Lean interface pass, check:

| item | required answer |
|---|---|
| Did any route module define source objects? | no |
| Are compact records constructed from expanded packages? | yes |
| Are common test equalities named? | yes |
| Is the lambda-window bridge named? | yes |
| Is finite-prime normalization pointwise? | yes |
| Does trace legality precede trace read-off? | yes |
| Is `QW = -sum_v W_v` named? | yes |
| Is source RH transported to Mathlib RH? | yes |
| Did `lake build ConnesWeilRH` pass? | yes |
| Did the axiom audit remain clean? | yes |

## Current Judgment

| question | answer |
|---|---|
| Is this audit a Lean implementation? | no |
| Does it define the next Lean pass gate? | yes |
| Does it allow compact records to remain primitive? | no |
| Does it prove RH? | no |

The next Lean interface pass should be rejected if it cannot pass this audit.
