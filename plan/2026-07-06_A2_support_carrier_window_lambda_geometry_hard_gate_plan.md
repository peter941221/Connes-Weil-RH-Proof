# A2 support carrier / window / lambda geometry hard-gate plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane A2.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

A2 is solved only if the active route-facing CCM24 source package gets
support/window/lambda facts from point-level coordinate geometry, not from a
package endpoint or a generic subset shortcut.

```text
old weak path:
  SourceSupportWindowData.windowContainedInLambda_of_one_lt
    used directly in SourceSupportWindowData.toCCM24SemilocalObjectPackage
    or SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows
    -> Source.ccm24_source_window_contained_in_lambda
    -> Route.Definitions.SourceBackedFixedSTest.windowContainedInLambda

new semantic owner/API:
  SourceConcreteBaseLayer pointInConcreteWindow facts
  SourceSupportWindowData.coordinateWindowCarrier / lambdaCarrier geometry
  SourceFixedWindowCoordinateRows support coordinate rows
  SourceModelConstructorInput.sourceWindowContainedInLambda
  SourceModelConstructorInput.sourceLambdaCompatible

real consumer rewired:
  SourceSupportWindowData.toCCM24SemilocalObjectPackage
  SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows
  SourceModelConstructorInput.toCCM24SourceModel
  Source.ccm24_source_window_contained_in_lambda
  Source.ccm24_source_lambda_compatible
  SourceBackedFixedSTest.ofExpandedSourcePackage

same-object alias / wrapper rejection scan:
  rg -n "windowContainedInLambda := fun I lambda hlambda =>|windowContainedInLambda_of_one_lt|sourceWindowContainedInLambdaData|sourceSupportInWindowData|sourceFourierSupportInWindowData|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

smallest WSL build:
  lake env lean ConnesWeilRH/Source/AnalyticCoreBase.lean
  lake env lean ConnesWeilRH/Source/AnalyticCore.lean
  lake build ConnesWeilRH.Source.AnalyticCore \
    ConnesWeilRH.Source.AnalyticSourceModel \
    ConnesWeilRH.Source.CCM24SourceModel \
    ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  SourceConcreteBaseLayer.mem_concreteSupportCarrier_iff
  SourceConcreteBaseLayer.pointInConcreteWindow_of_mem_concreteSupportCarrier
  SourceConcreteBaseLayer.mem_concreteSupportCarrier_coordinateLower
  SourceConcreteBaseLayer.mem_concreteSupportCarrier_coordinateUpper
  SourceConcreteBaseLayer.mem_concreteSupportCarrier_logScale_eq_zero
  SourceSupportWindowData.mem_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
  SourceSupportWindowData.coordinateWindowCarrier_eq_windowCarrier
  SourceSupportWindowData.lambdaCarrier_eq_setOf_pointInLambdaCutoff
  SourceSupportWindowData.coordinateWindowCarrier_subset_lambdaCarrier
  SourceSupportWindowData.windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
  SourceSupportWindowData.lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
  SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportCoordinateLower
  SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportCoordinateUpper
  SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportLogScale_eq_zero
  SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportInWindow
  SourceModelConstructorInput.sourceSupportInWindow
  SourceModelConstructorInput.sourceWindowContainedInLambda
  SourceModelConstructorInput.sourceLambdaCompatible
  Source.ccm24_source_window_contained_in_lambda
  Source.ccm24_source_lambda_compatible

semantic sufficiency for next route/RH step:
  The route-facing fixed-S object must receive window/lambda compatibility from
  coordinate lower/upper/logScale rows. The old generic one-lt containment can
  remain only as a derived compatibility theorem outside the active A2 route.
```

Rejected as not solved:

```text
1. `CCM24SourceModel.lean` still fills an active package constructor field by
   calling `SourceSupportWindowData.windowContainedInLambda_of_one_lt`.

2. The route path audits only `Source.ccm24_source_window_contained_in_lambda`
   while the package constructor behind it still hides point geometry.

3. The patch proves only a subset theorem and never exposes supportCarrier
   membership -> coordinate lower/upper/logScale rows.

4. The patch uses `True`, `Set.univ`, a zero carrier, a renamed `Prop`, or an
   endpoint package field to satisfy support/window/lambda containment.

5. The report says A2 solved while A1 raw-kernel semantics still supplies the
   support membership fact. Use `A2 geometry solved, A1 still open` instead.
```


## 2. Result Target

A2 is solved when the active CCM24 source route derives support carrier,
window carrier, and lambda carrier membership from point-level geometry.

```text
support carrier membership
  |
  +-- supportValue f x != 0
      |
      +-- concrete pointInConcreteWindow I x
          |
          +-- coordinate lower bound
          +-- coordinate upper bound
          +-- logScale x = 0
              |
              +-- coordinateWindowCarrier I
                  |
                  +-- windowCarrier I
                      |
                      +-- lambdaCarrier lambda, when 1 < lambda
                          |
                          +-- CCM24SourceModel.windowContainedInLambda
```

This lane does not solve A1 raw kernel semantics. A1 must prove that the raw
support kernel under `SourceSupportClosedWindowZeroKernelModel` has a concrete
pre-cutoff owner. A2 starts after membership evidence reaches point-level
support geometry.


## 3. Evidence Snapshot

Ledger source:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:76-82
  A2. support carrier / window / lambda geometry
    supportCarrier
    windowCarrier
    lambdaCarrier
    coordinate lower / upper rows
    logScale = 0 rows
```

Current memory says the window-lambda row has a verified cut:

```text
MEMORY.md:164-245
  CCM24 window-lambda source-model cut moved the row off package endpoints.
  SourceConcreteBaseLayer owns concrete windowCarrier/lambdaCarrier facts.
  Focused axiom audit for the listed declarations returned:
    [propext, Classical.choice, Quot.sound]
```

Project rules keep A2 on point rows, not subset wrappers:

```text
AGENTS.md:1430-1435
  supportMember_sourceTest_coordinateLower
  supportMember_sourceTest_coordinateUpper
  supportMember_sourceTest_logScale_eq_zero
```

The current source model already has the lower point facts:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean:3274
  mem_concreteSupportCarrier_iff

ConnesWeilRH/Source/AnalyticCoreBase.lean:3287-3304
  mem_concreteSupportCarrier_coordinateLower
  mem_concreteSupportCarrier_coordinateUpper
  mem_concreteSupportCarrier_logScale_eq_zero

ConnesWeilRH/Source/AnalyticCoreBase.lean:3480-3524
  pointInConcreteWindow_mem_concreteWindowCarrier
  mem_concreteWindowCarrier_iff_pointInConcreteWindow
  concreteWindowCarrier_eq_setOf_pointInConcreteWindow

ConnesWeilRH/Source/AnalyticCoreBase.lean:3530-3561
  pointInConcreteWindow_mem_concreteLambdaCarrier_of_one_lt
  concreteWindowCarrier_subset_lambdaCarrier_of_one_lt
  concreteWindowContainedInLambda_of_one_lt
  concreteLambdaCompatible_of_one_lt
```

Active rows currently expose support-side point facts:

```text
ConnesWeilRH/Source/AnalyticCore.lean:565-595
  SourceFixedWindowCoordinateRows.supportCoordinateLower
  SourceFixedWindowCoordinateRows.supportCoordinateUpper
  SourceFixedWindowCoordinateRows.supportLogScale_eq_zero

ConnesWeilRH/Source/AnalyticCore.lean:633-653
  SourceFixedWindowCoordinateRows.supportCarrier_subset_windowCarrier
  SourceFixedWindowCoordinateRows.supportInWindow
  SourceFixedWindowCoordinateRows.supportTransported
```


## 4. Current Risk

A2 can look solved through a high-level theorem while the active route still
skips the point geometry. The risky shape is:

```text
windowContainedInLambda I lambda
  |
  +-- generic subset proof
      |
      +-- no visible supportCarrier membership
      +-- no visible coordinate lower / upper rows
      +-- no visible logScale = 0 row
```

The completion gate must force this path:

```text
supportCarrier sourceTest
  |
  +-- supportValue != 0
      |
      +-- pointInConcreteWindow
          |
          +-- pointCoordinate between lower and upper endpoint
          +-- logScale = 0
              |
              +-- supportScale = 1
                  |
                  +-- lambda^-1 <= supportScale <= lambda
```

Do not mark A2 solved from a bare subset theorem. A subset theorem can stay as a
derived compatibility theorem after the point facts pass focused audit.


## 5. Detailed Gate Checklist

A2 is solved only if all gates below pass.

### Gate A. Support carrier membership has concrete point semantics

Required concrete theorem path:

```text
mem_concreteSupportCarrier_iff
  x in supportCarrier f <->
    pointInConcreteWindow I x and f x.1 != 0

pointInConcreteWindow_of_mem_concreteSupportCarrier
mem_concreteSupportCarrier_coordinateLower
mem_concreteSupportCarrier_coordinateUpper
mem_concreteSupportCarrier_logScale_eq_zero
```

Rejected:

```text
supportCarrier := Set.univ
supportCarrier membership supplied by a free Prop field
supportCarrier_subset_windowCarrier used as the only source fact
supportMember/sourceSupportMember wrapper families with no active consumer
```

### Gate B. Window carrier is tied to coordinate geometry

Required theorem path:

```text
mem_windowCarrier_iff
mem_coordinateWindowCarrier_iff
mem_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
mem_coordinateWindowCarrier_windowCarrier
mem_windowCarrier_coordinateWindowCarrier
coordinateWindowCarrier_eq_windowCarrier
```

Concrete readback:

```text
pointInConcreteWindow_mem_concreteWindowCarrier
mem_concreteWindowCarrier_pointInWindow
mem_concreteWindowCarrier_iff_pointInConcreteWindow
concreteWindowCarrier_eq_setOf_pointInConcreteWindow
```

This gate fails if the proof uses `windowCarrier := Set.univ`, a package field,
or a theorem-source axiom.

### Gate C. Lambda carrier is real cutoff geometry

Required theorem path:

```text
lambdaCarrier lambda = {x | pointInLambdaCutoff x lambda}
pointInLambdaCutoff x lambda <->
  lambda^-1 <= supportScale x and supportScale x <= lambda

pointInLambdaCutoff_of_supportScale_eq_one
mem_lambdaCarrier_of_supportScale_eq_one
coordinateWindowPoint_mem_lambdaCarrier
coordinateWindowCarrier_subset_lambdaCarrier
windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
```

Concrete readback:

```text
concreteSupportScale_eq_exp
concreteSupportScale_eq_one_of_second_eq_zero
pointInConcreteWindow_mem_concreteLambdaCarrier_of_one_lt
concreteWindowCarrier_subset_lambdaCarrier_of_one_lt
concreteWindowContainedInLambda_of_one_lt
concreteLambdaCompatible_of_one_lt
```

Rejected:

```text
lambdaCarrier := Set.univ
lambdaCarrier membership hidden behind True
lambda containment supplied by sourceWindowContainedInLambdaData package field
```

### Gate D. Active source rows consume point geometry

Required active path:

```text
SourceFixedWindowCoordinateRows.supportCoordinateLower
SourceFixedWindowCoordinateRows.supportCoordinateUpper
SourceFixedWindowCoordinateRows.supportLogScale_eq_zero
  |
  +-- SourceSupportCoordinateScaleModel.supportValue_coordinateLower
  +-- SourceSupportCoordinateScaleModel.supportValue_coordinateUpper
  +-- SourceSupportCoordinateScaleModel.supportValue_logScale_eq_zero
      |
      +-- SourceSupportClosedWindowZeroKernelModel.toCoordinateScaleModel
```

Then:

```text
SourceFixedWindowCoordinateRows.supportInWindow
SourceFixedWindowCoordinateRows.supportTransported
SourceSemilocalRows.sourceSupportInWindow
SourceModelConstructorInput.sourceSupportInWindow
```

The generic row may still abstract over the support-kernel provider. A1 owns
the remaining raw-kernel proof below that provider.

### Gate E. CCM24 source-model row uses source-model ownership

Required:

```text
CCM24SourceModel.windowContainedInLambda
Source.ccm24_source_window_contained_in_lambda
Source.ccm24_source_lambda_compatible
Route.Definitions.SourceBackedFixedSTest.windowContainedInLambda
Route.Definitions.SourceBackedFixedSTest.lambdaCompatible
```

The active package constructors must not hide the proof behind the old generic
one-lt shortcut:

```text
SourceSupportWindowData.toCCM24SemilocalObjectPackage
SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows
SourceModelConstructorInput.toCCM24SourceModel
```

Rejected active constructor proof:

```lean
windowContainedInLambda := fun I lambda hlambda =>
  SourceSupportWindowData.windowContainedInLambda_of_one_lt ...
```

Accepted active constructor proof:

```lean
windowContainedInLambda := fun I lambda hlambda =>
  SourceSupportWindowData.windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt ...
```

or a named theorem with the same coordinate-window/lambda dependency path.

The package endpoint fields must stay removed from active structures or remain
as compatibility-only theorem accessors:

```text
sourceWindowContainedInLambdaData
sourceSupportInWindowData
sourceFourierSupportInWindowData
```

Compatibility accessors may remain only if scans show no active constructor or
route path depends on them.


## 6. Implementation Batches

### Batch 1. Pin local types

Run a scratch Lean check before editing:

```lean
import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.AnalyticSourceModel
import ConnesWeilRH.Source.CCM24SourceModel

#check SourceSupportWindowData.supportCarrier
#check SourceSupportWindowData.windowCarrier
#check SourceSupportWindowData.coordinateWindowCarrier
#check SourceSupportWindowData.lambdaCarrier
#check SourceSupportWindowData.pointInLambdaCutoff
#check SourceSupportWindowData.coordinateWindowCarrier_subset_lambdaCarrier
#check SourceSupportWindowData.windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
#check SourceConcreteBaseLayer.mem_concreteSupportCarrier_iff
#check SourceConcreteBaseLayer.mem_concreteSupportCarrier_coordinateLower
#check SourceConcreteBaseLayer.mem_concreteSupportCarrier_coordinateUpper
#check SourceConcreteBaseLayer.mem_concreteSupportCarrier_logScale_eq_zero
```

Do not keep scratch checks in accepted code.

### Batch 2. Verify or add support membership readbacks

Owner:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean
namespace SourceConcreteBaseLayer
```

Required declarations:

```text
mem_concreteSupportCarrier_iff
pointInConcreteWindow_of_mem_concreteSupportCarrier
mem_concreteSupportCarrier_coordinateLower
mem_concreteSupportCarrier_coordinateUpper
mem_concreteSupportCarrier_logScale_eq_zero
concreteSupportCarrier_eq_setOf_pointInWindow_value_ne_zero
```

If all names already exist, do not add aliases. Add missing point-level readback
theorems only when a consumer needs them.

### Batch 3. Verify or add window geometry readbacks

Owner:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean
namespace SourceSupportWindowData
namespace SourceConcreteBaseLayer
```

Required declarations:

```text
mem_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
mem_coordinateWindowCarrier_windowCarrier
mem_windowCarrier_coordinateWindowCarrier
coordinateWindowCarrier_eq_windowCarrier
pointInConcreteWindow_mem_concreteWindowCarrier
mem_concreteWindowCarrier_iff_pointInConcreteWindow
concreteWindowCarrier_eq_setOf_pointInConcreteWindow
```

The proof path must use lower/upper/logScale rows. Do not replace these rows
with one `subset` input.

### Batch 4. Verify or add lambda geometry readbacks

Owner:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean
```

Required declarations:

```text
lambdaCarrier_eq_setOf_pointInLambdaCutoff
lambdaCarrier_eq_setOf_bounds
pointInLambdaCutoff_of_supportScale_eq_one
mem_lambdaCarrier_of_supportScale_eq_one
coordinateWindowPoint_mem_lambdaCarrier
coordinateWindowCarrier_subset_lambdaCarrier
windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
```

Concrete declarations:

```text
concreteSupportScale_eq_exp
concreteSupportScale_eq_one_of_second_eq_zero
pointInConcreteWindow_mem_concreteLambdaCarrier_of_one_lt
concreteWindowCarrier_subset_lambdaCarrier_of_one_lt
concreteWindowContainedInLambda_of_one_lt
concreteLambdaCompatible_of_one_lt
```

### Batch 5. Rewire active source rows to point geometry

Owner:

```text
ConnesWeilRH/Source/AnalyticCore.lean
ConnesWeilRH/Source/AnalyticSourceModel.lean
ConnesWeilRH/Source/CCM24SourceModel.lean
```

Required active route:

```text
SourceFixedWindowCoordinateRows.supportCoordinateLower
SourceFixedWindowCoordinateRows.supportCoordinateUpper
SourceFixedWindowCoordinateRows.supportLogScale_eq_zero
  |
  +-- supportCarrier_subset_coordinateWindowCarrier
      |
      +-- supportCarrier_subset_windowCarrier
          |
          +-- supportInWindow
              |
              +-- SourceSemilocalRows.sourceSupportInWindow
              +-- SourceModelConstructorInput.sourceSupportInWindow
```

For lambda:

```text
SourceModelConstructorInput.sourceWindowContainedInLambda
SourceModelConstructorInput.sourceLambdaCompatible
SourceModelConstructorInput.toCCM24SourceModel.windowContainedInLambda
SourceSupportWindowData.toCCM24SemilocalObjectPackage.windowContainedInLambda
SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows.windowContainedInLambda
```

These rows should use coordinate-window/lambda carrier theorems:

```text
windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
```

The older `windowContainedInLambda_of_one_lt` may remain as a compatibility
theorem only after focused audit shows it derives from window/carrier geometry.
It must not remain the active package-constructor proof in
`CCM24SourceModel.lean`.

### Batch 6. Remove or quarantine endpoint paths

Run:

```powershell
rg -n "sourceWindowContainedInLambdaData|sourceSupportInWindowData|sourceFourierSupportInWindowData" ConnesWeilRH -g "*.lean"
rg -n "supportMember|sourceSupportMember|supportCarrier_subset_coordinateWindowCarrier\\s*:" ConnesWeilRH\\Source -g "*.lean"
rg -n "windowContainedInLambda := fun I lambda hlambda =>|windowContainedInLambda_of_one_lt" ConnesWeilRH\\Source\\CCM24SourceModel.lean ConnesWeilRH\\Source\\AnalyticSourceModel.lean
rg -n "Set\\.univ|\\bTrue\\b" ConnesWeilRH\\Source\\AnalyticCoreBase.lean ConnesWeilRH\\Source\\AnalyticCore.lean ConnesWeilRH\\Source\\AnalyticSourceModel.lean ConnesWeilRH\\Source\\CCM24SourceModel.lean
```

Acceptance:

```text
No active structure field, constructor input, or route path uses the old
package endpoint fields.

No new support/lambda proof uses Set.univ or True.

Subset names remain only as derived theorems whose proof path exposes point
rows.

Any remaining `windowContainedInLambda_of_one_lt` hit must be documented as a
compatibility theorem outside the active A2 route path.
```


## 7. Focused Axiom Audit Targets

Use one scratch file after the smallest owning build passes:

```lean
import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.AnalyticSourceModel
import ConnesWeilRH.Source.CCM24SourceModel

#print axioms SourceConcreteBaseLayer.mem_concreteSupportCarrier_iff
#print axioms SourceConcreteBaseLayer.pointInConcreteWindow_of_mem_concreteSupportCarrier
#print axioms SourceConcreteBaseLayer.mem_concreteSupportCarrier_coordinateLower
#print axioms SourceConcreteBaseLayer.mem_concreteSupportCarrier_coordinateUpper
#print axioms SourceConcreteBaseLayer.mem_concreteSupportCarrier_logScale_eq_zero
#print axioms SourceConcreteBaseLayer.concreteSupportCarrier_eq_setOf_pointInWindow_value_ne_zero
#print axioms SourceConcreteBaseLayer.pointInConcreteWindow_mem_concreteWindowCarrier
#print axioms SourceConcreteBaseLayer.mem_concreteWindowCarrier_iff_pointInConcreteWindow
#print axioms SourceConcreteBaseLayer.concreteWindowCarrier_eq_setOf_pointInConcreteWindow
#print axioms SourceConcreteBaseLayer.concreteSupportScale_eq_exp
#print axioms SourceConcreteBaseLayer.concreteSupportScale_eq_one_of_second_eq_zero
#print axioms SourceConcreteBaseLayer.pointInConcreteWindow_mem_concreteLambdaCarrier_of_one_lt
#print axioms SourceConcreteBaseLayer.concreteWindowCarrier_subset_lambdaCarrier_of_one_lt
#print axioms SourceConcreteBaseLayer.concreteWindowContainedInLambda_of_one_lt
#print axioms SourceConcreteBaseLayer.concreteLambdaCompatible_of_one_lt
#print axioms SourceSupportWindowData.mem_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
#print axioms SourceSupportWindowData.coordinateWindowCarrier_eq_windowCarrier
#print axioms SourceSupportWindowData.lambdaCarrier_eq_setOf_pointInLambdaCutoff
#print axioms SourceSupportWindowData.coordinateWindowCarrier_subset_lambdaCarrier
#print axioms SourceSupportWindowData.windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
#print axioms SourceSupportWindowData.lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
#print axioms SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportCoordinateLower
#print axioms SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportCoordinateUpper
#print axioms SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportLogScale_eq_zero
#print axioms SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportCarrier_subset_windowCarrier
#print axioms SourceSupportWindowData.SourceFixedWindowCoordinateRows.supportInWindow
#print axioms SourceModelConstructorInput.sourceSupportInWindow
#print axioms SourceModelConstructorInput.sourceWindowContainedInLambda
#print axioms SourceModelConstructorInput.sourceLambdaCompatible
#print axioms Source.ccm24_source_window_contained_in_lambda
#print axioms Source.ccm24_source_lambda_compatible
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local theorem-source axiom
constant
opaque
unsafe
new free Prop field
```


## 8. Build And Static Gates

Use WSL Ubuntu-24.04 only.

Sync:

```bash
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'
```

Smallest build sequence:

```bash
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Source/AnalyticCoreBase.lean'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Source/AnalyticCore.lean'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.AnalyticCore ConnesWeilRH.Source.AnalyticSourceModel ConnesWeilRH.Source.CCM24SourceModel'
```

Route-facing gate:

```bash
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Route.RouteTheorem'
```

Static checks:

```powershell
git diff --check
rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b|\\bTrue\\b|Set\\.univ" ConnesWeilRH\\Source\\AnalyticCoreBase.lean ConnesWeilRH\\Source\\AnalyticCore.lean ConnesWeilRH\\Source\\AnalyticSourceModel.lean ConnesWeilRH\\Source\\CCM24SourceModel.lean
rg -n "sourceWindowContainedInLambdaData|sourceSupportInWindowData|sourceFourierSupportInWindowData" ConnesWeilRH -g "*.lean"
rg -n "windowContainedInLambda := fun I lambda hlambda =>|windowContainedInLambda_of_one_lt|Source\\.ccm24_source_window_contained_in_lambda|Source\\.ccm24_source_lambda_compatible" ConnesWeilRH\\Source ConnesWeilRH\\Route -g "*.lean"
```

The `True` scan may report pre-existing CC20 trace-normalization placeholders in
`AnalyticCore.lean`. The A2 report must show those hits stay outside the A2
dependency path.


## 9. Acceptance Map

Use this block when reporting A2 completion:

```text
final or route-level obligation:
  CCM24 source/window/model rows feeding CCM24SourceModel.windowContainedInLambda,
  SourceModelConstructorInput.sourceSupportInWindow, and route CCM24 lambda
  compatibility.

current weak statement / old path:
  Package endpoint fields and subset-style support/window/lambda statements can
  hide point geometry.

why the current statement is insufficient:
  A2 needs support carrier membership to expose coordinate lower/upper and
  logScale = 0 before deriving window and lambda membership.

stronger semantic owner/API needed:
  SourceConcreteBaseLayer pointInConcreteWindow and SourceSupportWindowData
  coordinateWindowCarrier / lambdaCarrier point theorems.

consumer that will be rewired or verified:
  SourceFixedWindowCoordinateRows support point rows,
  SourceSemilocalRows.sourceSupportInWindow,
  SourceModelConstructorInput.sourceSupportInWindow,
  SourceModelConstructorInput.sourceWindowContainedInLambda,
  SourceModelConstructorInput.toCCM24SourceModel.windowContainedInLambda,
  SourceSupportWindowData.toCCM24SemilocalObjectPackage,
  SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows,
  Source.ccm24_source_window_contained_in_lambda,
  SourceBackedFixedSTest.ofExpandedSourcePackage.

old path that will be deleted or demoted:
  sourceWindowContainedInLambdaData, sourceSupportInWindowData, and
  sourceFourierSupportInWindowData remain absent from active fields and route
  consumers. `windowContainedInLambda_of_one_lt` remains derived compatibility
  only and is not the active package-constructor proof. Subset theorems remain
  derived compatibility only.

why the new statement can feed the RH route:
  The CCM24 source model gets lambda/window compatibility from concrete support
  carrier geometry instead of endpoint package assumptions.

smallest WSL build:
  lake env lean ConnesWeilRH/Source/AnalyticCoreBase.lean
  lake env lean ConnesWeilRH/Source/AnalyticCore.lean
  lake build ConnesWeilRH.Source.AnalyticCore
    ConnesWeilRH.Source.AnalyticSourceModel
    ConnesWeilRH.Source.CCM24SourceModel
  lake build ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  listed in section 6.
```


## 10. Rejection Rules

Reject the batch if any item is true:

```text
1. The patch proves only supportCarrier_subset_windowCarrier or
   windowCarrier_subset_lambdaCarrier and does not expose point-level
   coordinate lower/upper/logScale rows.

2. The patch reintroduces sourceWindowContainedInLambdaData,
   sourceSupportInWindowData, or sourceFourierSupportInWindowData as active
   structure fields or constructor inputs.

3. The patch uses Set.univ, True, a zero carrier, or a renamed Prop to satisfy
   support/window/lambda containment.

4. The active CCM24 route stops at package endpoint theorem accessors.

4A. `CCM24SourceModel.lean` still fills active package `windowContainedInLambda`
    fields through `SourceSupportWindowData.windowContainedInLambda_of_one_lt`.

5. The focused axiom audit exposes sorryAx, a project-local theorem-source
   axiom, constant, opaque, unsafe, or a new free Prop field.

6. The report says A2 solved while A1 raw kernel remains the hidden reason that
   support carrier membership holds. In that case, mark A2 geometry solved
   relative to the current support-value provider and keep A1 open.
```


## 11. Completion Labels

Use one of these labels after implementation or verification.

```text
A2 solved:
  active CCM24 source rows derive support carrier -> window -> lambda from
  point-level coordinate bounds and logScale = 0. Source and route builds pass,
  and focused axioms are clean.

A2 geometry solved, A1 still open:
  A2 point geometry and lambda containment are clean, but support membership
  still depends on the raw-kernel provider covered by A1.

A2 not solved:
  active route uses package endpoint rows, subset-only wrappers, Set.univ,
  True, a renamed Prop field, or unaudited project-local theorem sources.
```
