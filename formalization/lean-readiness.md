# Lean Readiness Map

Status: segmented phase-1 scaffold builds, not yet a Lean proof.

## What It Is

This file converts the current manuscript into a Lean-start plan.

The purpose is not to prove the analytic source papers inside Lean first. The
purpose is to make the route theorem formalizable from explicit imported source
interfaces.

The current scaffold has reached that first engineering shape:

```text
lake build ConnesWeilRH
```

passes on the WSL ext4 mirror. The final route theorem concludes Mathlib's
`_root_.RiemannHypothesis`.

## Why This Is The Right Next Step

The manuscript now separates the proof into three layers:

```text
source theorems
  |
  v
project lemmas
  |
  v
route theorem
```

Lean should mirror that split. If the first Lean pass tries to formalize all of
CCM24, CCM25, and CC20, the project will stall on analytic infrastructure before
testing the route composition. If the first Lean pass axiomatizes the imported
source theorems with exact hypotheses, Lean can check whether the manuscript's
own implication chain is coherent.

## Start Criteria

Lean work may start when these are true:

| criterion | current status | evidence |
|---|---|---|
| Manuscript has a stable theorem spine | pass | `docs/manuscripts/connes-weil-rh-proof-draft.md` Proof Spine |
| Theorem 1 has explicit admissibility hypotheses | pass | `Admissible Windows For Theorem 1` |
| Positive trace is trace-class before non-negativity is used | pass | Lemma 2 and Theorem 1 Step 1 |
| Source-line audit exists | pass | manuscript source-line audit plus `docs/audits/source-reread-v0.2.md` |
| External source theorems can be separated from project lemmas | pass | Dependency and non-circularity audit |
| First Lake scaffold scope is documented | pass | Recommended First Lean Scaffold |

## Recommended First Lean Scaffold

The first scaffold uses these files:

```text
lakefile.toml
lean-toolchain
ConnesWeilRH.lean
ConnesWeilRH/
  Basic.lean
  Source/
    CCM24.lean
    CCM25.lean
    CC20.lean
  Route/
    Definitions.lean
    AdmissibleWindow.lean
    Ledger.lean
    Theorem1.lean
    Exhaustion.lean
    RouteTheorem.lean
```

The first build contains theorem statements, structures, and imported
source-interface records only. Analytic proofs remain later work.

## Phase 1 Proof Target

Phase 1 should prove the following conditional theorem:

```text
Assuming the CCM24, CCM25, and CC20 source interfaces,
the project route lemmas imply RH.
```

This matches the manuscript's current boundary. It does not claim journal,
Clay, or full analytic Lean certification.

## Non-Negotiable Proof Hygiene

The final Connes-Weil route must be audit-clean in Lean.

| gate | required evidence |
|---|---|
| Final target is standard RH | theorem conclusion is `_root_.RiemannHypothesis` |
| Project RH wrappers do not drift | wrappers are abbreviations or have equivalence lemmas to Mathlib RH |
| Custom objects are not private inventions | each route object has a bridge theorem to the manuscript/source notation |
| Source assumptions are quarantined | all source-paper assumptions live under `ConnesWeilRH/Source/` |
| No hidden proof debt | route modules contain no `sorry`, `admit`, `axiom`, `constant`, `opaque`, or `unsafe` outside source interfaces |
| Axiom boundary is public | `#print axioms <final_theorem>` is recorded in a repository audit file |
| Unreviewed toy material stays out of the route | final Connes-Weil imports do not depend on unaudited toy modules |

The intended audit shape is:

```text
#print axioms final_connes_weil_rh
  |
  v
only:
  Mathlib/kernel foundations
  CCM24 source interface
  CCM25 source interface
  CC20 source interface
```

Any extra project axiom means the artifact is not ready for serious external
review.

## Suggested Lean Object Model

| manuscript object | Lean representation | reason |
|---|---|---|
| finite set `S` containing infinity | structure field or predicate `IsFinitePlaceSet S` | keeps fixed-`S` assumptions explicit |
| interval `I` and `lambda` | structure `AdmissibleWindow` | Theorem 1 should take one bundled hypothesis |
| test function `g` | abstract type with support and transform fields in phase 1 | avoids premature analytic infrastructure |
| `F_g=g^* * g` | function attached to a test object | finite-prime visibility depends on it |
| prime visibility condition | predicate `VisiblePrimesCovered S g` | prevents fixed-`S`/full-`QW` mismatch |
| `PositiveTrace` | nonnegative scalar supplied by a source/project theorem | first pass checks route logic |
| rank/pole ledgers | scalar fields with vanishing lemmas | triple-kill step becomes formal and local |
| `Cdef` | nonnegative or norm-controlled error scalar | exhaustion theorem can consume it explicitly |
| `QW_lambda` and `QW` | abstract quadratic-form functions | source formula and convergence can be separate |
| finite vanishing set `{0,1/2,1}` | explicit finite set object | needed for CC20 Proposition C.1 interface |

## Phase 1 Module Dependencies

```text
Source.CCM24
Source.CCM25
Source.CC20
      |
      v
Route.Definitions
      |
      v
Route.AdmissibleWindow
      |
      v
Route.Ledger
      |
      v
Route.Theorem1
      |
      v
Route.Exhaustion
      |
      v
Route.RouteTheorem
```

## Phase 1 Non-Goals

Do not try to prove these in the first Lean pass:

| non-goal | reason |
|---|---|
| full CCM24 semilocal analysis | source theorem, large analytic dependency |
| full CC20 trace-class proof | source theorem, requires serious operator theory |
| full CCM25 explicit formula derivation | source theorem, not project-owned |
| numerical or experimental checks | irrelevant to route formalization |
| public proof certification | requires external review and later Lean phases |

## First Formalization Gate

The first Lean milestone is complete when the segmented route target:

```text
lake build ConnesWeilRH
```

passes for a scaffold in which:

1. the source theorem interfaces are declared,
2. `AdmissibleWindow` bundles the Theorem 1 hypotheses,
3. Theorem 1 is stated with explicit ledger terms,
4. Theorem 2 consumes the triple vanishing hypotheses,
5. Theorem 3 consumes exhaustion hypotheses,
6. Theorem 4 consumes the CC20 finite-vanishing RH exit interface,
7. the route theorem composes the chain without hidden assumptions,
8. `#print axioms` for the route theorem is recorded and contains no
   unapproved project-local axiom.

Use `lake build ConnesWeilRH` as the phase-1 gate so the verification scope
matches the current route target.

Current verification:

```text
lake build ConnesWeilRH
Build completed successfully (2909 jobs).
elapsed: about 3 seconds after the changed segments had rebuilt

#print axioms ConnesWeilRH.Route.final_connes_weil_rh
[propext, Classical.choice, Quot.sound]
```

The CC20 finite-vanishing RH exit now enters through
`ConnesWeilRH.FiniteVanishingCriterionPackage`, not through a route-local
certificate field.

The CC20 trace, trace-class, Mellin, and sign obligations now enter through
`ConnesWeilRH.ArchimedeanTraceSymbols`. This records the contract shape for the
archimedean trace layer. The actual operator model and trace-ideal proofs remain
future formalization work.

The CCM24 semilocal-model, support-transport, bounded-comparison, and
Sonin-comparison obligations now enter through
`ConnesWeilRH.SemilocalModelSymbols`. A scan of `ConnesWeilRH/Source` finds no
remaining `statement := True` obligations. The next Lean phase must connect
these symbolic contracts to source-paper analytic definitions or accepted
imports.

`RouteCertificate` now consumes
`ConnesWeilRH.Route.SourceBackedFixedSTest`. The route theorem derives
`AdmissibleForTheorem1` from
`ConnesWeilRH.Route.admissible_for_theorem1_of_source_backed`, so final-route
admissibility is no longer supplied as a standalone route-local field. This is
still a symbolic bridge: the semilocal symbols must later be replaced by or
proved equivalent to the CCM24 analytic objects.

Finite-prime visibility now uses the CCM25 finite-prime normalization interface.
`ConnesWeilRH.Route.finite_prime_visibility_statement_of_source_backed` derives
`ConnesWeilRH.WeilFormSymbols.FinitePrimeVisibilityStatement` from
`inputs.ccm25.finitePrimeNormalization`. The route-level predicate
`test.finitePrimesVisible` is then obtained through an explicit bridge field on
`SourceBackedFixedSTest`. Later phases should replace that bridge with a proved
equivalence once the test-function and finite-prime support objects are
formalized.

Full Weil positivity now uses `ConnesWeilRH.Route.SourceBackedFullPositivity`.
The bridge obtains the CC20 trace-square result from
`inputs.cc20.traceClassTemplate` and `inputs.cc20.archimedeanTraceSquare`,
obtains the CCM25 Weil-form read-off through a bridge fed by
`inputs.ccm25.qwDefinition`, `inputs.ccm25.qwLambdaFormula`, and
`inputs.ccm25.poleNormalization`, then produces
`ConnesWeilRH.Route.FullWeilPositivity` through
`ConnesWeilRH.Route.full_weil_positivity_of_source_backed`. The ledger fields
now pass through `ConnesWeilRH.Route.SourceBackedLedgers`: rank clearing uses
CCM24 bounded comparison plus CC20 sign normalization, pole clearing uses CCM25
pole normalization, and Cdef exhaustion uses CCM24 Sonin comparison plus CC20
Mellin convention. The ledger source propositions are still symbolic and must
later be tied to the manuscript's concrete rank, pole, and Cdef ledgers.

Triple vanishing now uses `ConnesWeilRH.CriticalVanishingPoint`, a finite type
with constructors `zero`, `half`, and `one`. `TripleVanishingSymbols` records
vanishing at those three points, and
`ConnesWeilRH.Route.triple_vanishing_of_source_backed` obtains the route-level
`test.tripleVanishing` predicate through an explicit bridge on
`SourceBackedFixedSTest`. Later phases should identify these constructors with
the manuscript's concrete points `{0, 1/2, 1}` in the chosen Mellin/Fourier
coordinate.

The fixed-S trace read-off bridge now uses
`ConnesWeilRH.Route.SourceTraceReadOffData`, which separates trace legality,
no-defect source read-off, Weil-form identification, and positive-trace
nonnegativity. The source-backed full positivity path feeds that structure with
the CC20 trace-square result and the CCM25 Weil-form read-off result before
producing `FixedSPositiveTraceReadOff`.

`FixedSPositiveTraceReadOff` is no longer definitionally equal to
`AdmissibleForTheorem1`. It now exists only when those four trace/read-off
components have been supplied. The next Lean phase should replace the remaining
symbolic trace/read-off propositions inside `SourceTraceReadOffData` with
operator-level statements tied to the CC20 and CCM25 source objects.

`SourceTraceReadOffData` now owns the CC20 archimedean test object and the
Hilbert-Schmidt gate. Theorems in `ConnesWeilRH.Route.Theorem1` derive
`CC20TraceLegality` and `CC20TraceSquareReadOff` from
`inputs.cc20.traceClassTemplate` and `inputs.cc20.archimedeanTraceSquare`.
This keeps trace-class legality inside the fixed-S Theorem 1 segment instead of
letting the downstream positivity bridge supply it.

The CCM25 Weil-form read-off now uses
`ConnesWeilRH.Route.CCM25WeilFormReadOff`. This proposition records the selected
source-backed fixed-`S` test, the restricted parameter `lambda`,
`WindowLambdaCompatibility`, the `QW` definition, the `Psi` sign formula, the
restricted `QW_lambda` formula, and pole normalization. `SourceTraceReadOffData`
stores `lambda` and `oneLtLambda`, and
`ConnesWeilRH.Route.ccm25_weil_form_read_off` derives the read-off from
`inputs.ccm25.qwDefinition`, `inputs.ccm25.qwLambdaFormula`, and
`inputs.ccm25.poleNormalization`. The route no longer carries a loose
`weilFormReadOff : Prop` field on `SourceBackedFullPositivity`.

`WindowLambdaCompatibility` binds `lambda` to the CCM24 window of the
source-backed fixed-`S` test. `lambda_compatible_of_source_backed` derives the
window compatibility from support transport, convolution-support transport, and
Sonin exhaustion, so the restricted parameter is no longer a route-local free
number.

Final Weil identification now has an intermediate
`ConnesWeilRH.Route.TraceWeilCompatibility` stage. `SourceTraceReadOffData`
first combines `CC20NoDefectSourceReadOff` with `CCM25WeilFormReadOff` through
`traceWeilCompatibilityBridge`; only after that does `weilIdentificationBridge`
produce the final identification. This keeps the no-defect trace equality and
the CCM25 formula read-off visible as a named junction.

`TraceWeilCompatibility` now carries two named read-off equalities:
`fullTraceReadOff`, which identifies the CC20 source no-defect trace with the
CCM25 `QW` value, and `restrictedTraceReadOff`, which identifies the CC20
support-square trace with the restricted CCM25 `QW_lambda` value. Later phases
should replace these symbolic equalities with operator-level trace/form
identification theorems.

The named read-off equalities now come through source bridge propositions.
`SourceTraceReadOffData` carries `FullTraceReadOffSource` and
`RestrictedTraceReadOffSource` witnesses, then obtains the two equalities through
`fullTraceReadOffBridge` and `restrictedTraceReadOffBridge`. This prevents the
trace/form equalities from being supplied as direct certificate fields.

The bridges now consume the concrete legs directly. `fullTraceReadOffBridge`
takes `CC20NoDefectSourceReadOff`, and `restrictedTraceReadOffBridge` takes
`CCM25WeilFormReadOff`. `SourceTraceReadOffData` no longer carries arbitrary
`fullTraceReadOffSource : Prop` or `restrictedTraceReadOffSource : Prop`
certificate fields.

The read-off equality targets now have their own names:
`FullTraceReadOffEquality` and `RestrictedTraceReadOffEquality`.
`FullTraceReadOffSource` and `RestrictedTraceReadOffSource` bundle a concrete
source leg with the corresponding equality. This gives later operator-level
trace/form identification proofs a precise replacement target.

The CCM25 read-off now splits into `CCM25FullQWReadOff` and
`CCM25RestrictedQWReadOff`. The full leg uses the CCM25 `QW` definition and
`Psi` sign formula; the restricted leg uses the `QW_lambda` formula, the
`lambda` window compatibility gate, and pole normalization. `CCM25WeilFormReadOff`
now bundles those two legs.

The CCM25 full and restricted legs now expose their sub-obligations. The full
leg contains `CCM25QWDefinitionReadOff` and `CCM25PsiSignReadOff`. The
restricted leg contains `WindowLambdaCompatibility`,
`CCM25QWLambdaFormulaReadOff`, and `CCM25PoleNormalizationReadOff`. Later
operator-level replacements can target those five names directly.

`WindowLambdaCompatibility` now carries `WindowSupportContainment`. That
package records source support in the CCM24 window, Fourier support in the same
window, convolution-support transport, and `windowContainedInLambda window
lambda`. The theorem `lambda_compatible_of_source_backed` still derives the
final `lambdaCompatible window lambda`, but the containment facts are no longer
hidden inside that final predicate.

The CCM25 finite-prime sums now use explicit symbolic index sets instead of
`Finset.range 0`. The full `Psi`/`QW` formula uses
`WeilFormSymbols.globalPrimeIndexSet`, and the restricted `QW_lambda` formula
uses `WeilFormSymbols.restrictedPrimeIndexSet lambda`. These fields remain
source-conditional, but they prevent the phase-1 scaffold from silently turning
finite-prime contributions into an empty sum.

## Source-Object Interface Phase

The source-interface discharge proof packages now have a source-object
replacement batch:

```text
docs/audits/source-object-replacement-consistency-audit.md
docs/audits/formal-gate-spine-consistency-audit.md
docs/audits/source-object-theorem-discharge-ledger.md
docs/proofs/source-object-definition-theorem-contract.md
docs/proofs/source-common-test-tuple-theorem-contract.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
docs/audits/sonin-prolate-defect-discharge-ledger.md
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/rh-definition-bridge-theorem-contract.md
```

The first audit checks four expanded packages:

```text
CCM24 semilocal objects
CCM25 finite-prime indices
CC20 trace objects
CC20 RH exit objects
```

The second audit checks the remaining formal gates as one ordered spine:

```text
source-definition
trace-legality
finite-prime normalization
final sign bridge
RH definition bridge
```

The source-object definition gate now has a theorem contract that fixes the
formal/import targets for the common test and convolution square, one fixed
`(S,I,lambda,g)` tuple, the CCM24 window controlling the restricted route,
CCM25 Weil objects, CC20 trace objects, CC20 RH-exit objects, and derivations
of the compact records currently consumed by the route.

The CC20 trace-legality gate now has a theorem contract that fixes the
formal/import targets for operator identity, Hilbert-Schmidt, trace-class
square, per-move cyclicity, support-square read-off, no-defect read-off, and
bounded-comparison trace-ideal transport.

The CCM25 finite-prime normalization gate now has a theorem contract that fixes
the formal/import targets for prime-power indices, global source support,
restricted lambda-cut support, visibility before the cut, fixed-S visible-prime
admissibility, von Mangoldt weight, source pairing, pointwise atom equality,
and finite-prime sign ownership.

The final sign bridge gate now has a theorem contract that fixes the
formal/import targets for common source test, `Psi` sign expansion,
archimedean sign bridge, finite-prime sign ownership, source pole sign in the
CC20 local sum, `QW(g,g)=-sum_v W_v(F_g)`, and
`QW(g,g)>=0 -> sum_v W_v(F_g)<=0`.

The RH definition bridge gate now has a theorem contract that fixes the
formal/import targets for source zeta equality with Mathlib `riemannZeta`,
zero transport in both directions needed by the bridge, negative-even
exclusion, pole exclusion, construction of the source non-trivial-zero witness
from Mathlib hypotheses, critical-line equivalence, and
`CC20SourceRH -> _root_.RiemannHypothesis`.

The next Lean step should not add more route scaffolding. It should encode the
expanded source-object boundary described in:

```text
formalization/source-object-interface-plan.md
```

Before treating that next Lean step as proof progress, use the two hard-blocker
audits as the current mathematical gate:

```text
docs/audits/sign-defect-blocker-audit.md
docs/audits/source-import-legitimacy-audit.md
```

Those audits keep two issues outside the scaffold: uncontrolled Sonin/prolate
defects, and source claims that are strategy or numerical evidence rather than
accepted theorem imports.

The two corresponding theorem contracts are:

```text
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
docs/audits/sonin-prolate-defect-discharge-ledger.md
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
```

The source-readiness split is now:

```text
docs/audits/sonin-prolate-defect-source-readiness-audit.md
  hard blocker remains open

docs/audits/restricted-to-full-qw-source-readiness-audit.md
  CCM25 restriction-definition path found after the bridge contract
```

The plan keeps the existing compact records:

```text
SemilocalModelSymbols
WeilFormSymbols
ArchimedeanTraceSymbols
FiniteVanishingCriterionPackage
```

as derived views of an expanded source-object package. This prevents the final
route from treating compact symbolic fields as source evidence.

This is still not full analytic formalization. The immediate goal is narrower:

```text
make the source-object dependency graph Lean-visible
without proving CCM24, CCM25, or CC20 analytic theorems yet.
```
