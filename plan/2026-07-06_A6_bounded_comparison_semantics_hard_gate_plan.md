# A6 Bounded Comparison Semantics Hard-Gate Plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane A6.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

A6 is solved only if the active CCM24 source-to-route path carries bounded
comparison as one concrete operator owner with inverse laws. A pair of separate
`boundedComparisonMap` and `boundedComparisonInverse` Prop witnesses does not
close the lane.

```text
old weak path:
  SourceSignedCoordinateComparisonData S H := Unit
    -> sourceBoundedComparisonModelData V H := ()
    -> SourceBoundedComparisonData / SourceBoundedComparisonEquivData wrapper
    -> boundedComparisonMap_of_data
    -> boundedComparisonInverse_of_data
    -> SourceBackedFixedSTest.boundedComparisonMap
    -> SourceBackedFixedSTest.boundedComparisonInverse
    -> bounded_comparison_of_source_backed
    -> PostQSeriesTailBoundedComparison

new semantic owner/API:
  SourceSignedCoordinateComparisonData must be a real structure, not an abbrev
  or namespace-defined operator family. It carries:
    coordinateComparisonEquiv
    coordinateComparisonEquiv_apply
    coordinateComparisonEquiv_involutive
    coordinateComparisonEquiv_symm_apply
    coordinateComparisonEquiv_comp_self

  SourceBoundedComparisonEquivData must carry the Hilbert-side transport:
    comparisonEquiv
    comparisonMap
    comparisonInverse
    comparisonMap_leftInverse
    comparisonMap_rightInverse
    comparisonMap_leftInverse_apply
    comparisonMap_rightInverse_apply

  Route.SourceBackedPostQBoundedComparisonData must be the route-facing owner
  for the source-backed path. It carries one source bounded-comparison data
  object, the old map/inverse Props derived from that object, and the two
  inverse-law readbacks from the same object.

  If `SourceObject.CCM24SemilocalObjectPackage` currently erases the
  source-level dependent data into `SemilocalModelSymbols`, the batch must add
  the smallest package/accessor field that preserves the source-place
  `SourceBoundedComparisonData` object before route construction. A route data
  record built only from the two old Props is rejected.

real consumer rewired:
  SourceSemilocalRows.sourceBoundedComparisonModelData
  SourceSemilocalRows.sourceBoundedComparisonMapData
  SourceSemilocalRows.sourceBoundedComparisonInverseData
  SourceSemilocalRows.sourceBoundedComparisonTraceClassTransport
  SourceModelConstructorInput.sourceBoundedComparisonModelData
  SourceModelConstructorInput.sourceBoundedComparisonData
  SourceBackedFixedSTest.ofExpandedSourcePackage
  SourceBackedPostQBoundedComparisonData.ofExpandedSourcePackage
  post_q_series_tail_bounded_comparison_of_source_backed_data
  bounded_comparison_of_source_backed
  PostQSeriesTailBoundedComparison

same-object alias / wrapper rejection scan:
  rg -n "abbrev SourceSignedCoordinateComparisonData|SourceSignedCoordinateComparisonData.*:=\\s*Unit|sourceBoundedComparisonModelData := by|exact \\(\\)|boundedComparisonMap := by|boundedComparisonInverse := by|boundedComparisonMap_of_data|boundedComparisonInverse_of_data|PostQSeriesTailBoundedComparison|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"

field-use / route-owner rejection scan:
  rg -n "_D : SourceSignedCoordinateComparisonData|\\(_D : SourceSignedCoordinateComparisonData|exact .*ContinuousLinearEquiv\\.refl|exact .* • ContinuousLinearEquiv\\.refl|PostQSeriesTailBoundedComparison inputs g lambda :=|post_q_series_tail_bounded_comparison_of_source_backed\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.AnalyticSourceModel \
    ConnesWeilRH.Source.CCM24SourceModel \
    ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_apply
  SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_involutive
  SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_symm_apply
  SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_comp_self
  SourceSignedCoordinateComparisonData.toEquivData
  SourceBoundedComparisonEquivData.comparisonMap
  SourceBoundedComparisonEquivData.comparisonInverse
  SourceBoundedComparisonEquivData.comparisonMap_leftInverse
  SourceBoundedComparisonEquivData.comparisonMap_rightInverse
  SourceBoundedComparisonEquivData.comparisonMap_leftInverse_apply
  SourceBoundedComparisonEquivData.comparisonMap_rightInverse_apply
  SourceBoundedComparisonData.comparisonMap_leftInverse_apply_of_data
  SourceBoundedComparisonData.comparisonMap_rightInverse_apply_of_data
  SourceSupportWindowData.boundedComparisonMap
  SourceSupportWindowData.boundedComparisonInverse
  SourceSupportWindowData.boundedComparisonMap_and_inverse_of_data
  SourceSemilocalRows.sourceBoundedComparisonMapData
  SourceSemilocalRows.sourceBoundedComparisonInverseData
  SourceSemilocalRows.sourceBoundedComparisonTraceClassTransport
  SourceModelConstructorInput.sourceBoundedComparisonData
  SourceConcreteBaseLayer.concreteRealSignedCoordinateComparisonData
  SourceConcreteBaseLayer.concreteRealBoundedComparisonData
  SourceConcreteBaseLayer.concreteRealBoundedComparisonMap
  SourceConcreteBaseLayer.concreteRealBoundedComparisonInverse
  SourceObject.CCM24SemilocalObjectPackage.sourceBackedBoundedComparisonData
  SourceBackedPostQBoundedComparisonData.ofExpandedSourcePackage
  post_q_series_tail_bounded_comparison_of_source_backed_data
  bounded_comparison_of_source_backed
  post_q_series_tail_bounded_comparison_of_source_backed

semantic sufficiency for next route/RH step:
  The route-side post-Q tail comparison must depend on a single bounded
  comparison equivalence whose map and inverse are proved inverse to each
  other. It must not depend only on two unrelated Prop witnesses that happen to
  be constructed from the same endpoint package.
```

Rejected as not solved:

```text
1. The active owner remains:
     SourceSignedCoordinateComparisonData := Unit

2. A constructor still fills bounded comparison with:
     sourceBoundedComparisonModelData := by intro _ _; exact ()

3. The patch proves local map/inverse lemmas but route consumers still receive
   only:
     inputs.ccm24.boundedComparisonMap placeSet
     inputs.ccm24.boundedComparisonInverse placeSet

4. The route tail theorem still treats bounded comparison as a pair of
   independent Props, with no theorem tying them to one comparisonEquiv.

5. The patch uses `True`, `Set.univ`, a free Prop field, endpoint package
   evidence, or a compatibility wrapper as the bounded-comparison meaning.

6. The patch replaces `Unit` with a structure but keeps the active coordinate
   comparison operator as a namespace definition that ignores the record
   argument.

7. The patch leaves `post_q_series_tail_bounded_comparison_of_source_backed`
   as the active source-backed route proof and does not add/use
   `post_q_series_tail_bounded_comparison_of_source_backed_data`.
```


## 2. Result First

Expected result:

```text
Good only if:
  A6 makes post-Q tail bounded comparison consume one bounded-comparison
  equivalence owner and its inverse laws through
  `SourceBackedPostQBoundedComparisonData`.

Partial only if:
  A6 audits local `comparisonMap` / `comparisonInverse` facts but leaves the
  active route path on the old Prop pair.

Rejected if:
  A6 only renames `SourceSignedCoordinateComparisonData := Unit`, adds a
  wrapper around `boundedComparisonMap_of_data`, or treats the endpoint package
  as proof that the map and inverse are semantically linked.
```

A6 is not about proving many algebraic facts around `ContinuousLinearEquiv`.
A6 is about making the active RH-route dependency stronger.


## 3. Current Evidence

Ledger source:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:106-112
  A6. bounded comparison semantics
    SourceBoundedComparisonData
    SourceBoundedComparisonEquivData
    SourceSignedCoordinateComparisonData
    comparisonMap / comparisonInverse
    inverse-law and operator-meaning owner
```

Current weak coordinate owner:

```text
ConnesWeilRH/Source/AnalyticCore.lean:3288-3292
  abbrev SourceSignedCoordinateComparisonData ... := Unit
```

Current Hilbert-side owner:

```text
ConnesWeilRH/Source/AnalyticCore.lean:3294-3301
  structure SourceBoundedComparisonEquivData ... where
    comparisonEquiv :
      H.hilbertCarrier ≃L[ℝ] H.hilbertCarrier
```

Current map/inverse definitions and inverse laws:

```text
ConnesWeilRH/Source/AnalyticCore.lean:3305-3357
  SourceBoundedComparisonEquivData.comparisonMap
  SourceBoundedComparisonEquivData.comparisonInverse
  comparisonMap_leftInverse
  comparisonMap_rightInverse
```

Current old predicates:

```text
ConnesWeilRH/Source/AnalyticCore.lean:4793-4829
  boundedComparisonMap S V : Prop
  boundedComparisonInverse S V : Prop
  boundedComparisonMap_of_data
  boundedComparisonInverse_of_data
  boundedComparisonMap_and_inverse_of_data
```

Current route consumer:

```text
ConnesWeilRH/Route/Definitions.lean:147-150
  SourceBackedFixedSTest.boundedComparisonMap
  SourceBackedFixedSTest.boundedComparisonInverse

ConnesWeilRH/Route/AdmissibleWindow.lean:110-114
  bounded_comparison_of_source_backed returns the Prop pair.

ConnesWeilRH/Route/SignDefect.lean:39-44
  PostQSeriesTailBoundedComparison inputs g lambda :=
    inputs.ccm24.boundedComparisonMap g.placeSet and
    inputs.ccm24.boundedComparisonInverse g.placeSet
```

Concrete coordinate comparison is currently a signed map:

```text
ConnesWeilRH/Source/AnalyticCore.lean
  concreteRealCoordinateSignedComparisonEquiv
  concreteRealCoordinateSignedComparisonEquiv_involutive

ConnesWeilRH/Source/AnalyticCore.lean:6525-6541
  concreteRealBoundedComparisonCoordinateData uses
    SourceSignedCoordinateComparisonData := ()

  concreteRealSignedCoordinateComparisonData := ()
```

The evidence says the project has a real equivalence layer, but the route still
forgets it into two old Props.


## 4. First-Principles Dependency Chain

```text
+--------------------------------------------------------------+
| Concrete coordinate comparison                                |
|                                                              |
|   coordinateComparisonEquiv x = -x                            |
|   coordinateComparisonEquiv (coordinateComparisonEquiv x) = x |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Hilbert-side transported equivalence                          |
|                                                              |
|   comparisonEquiv                                             |
|   comparisonMap := comparisonEquiv.toContinuousLinearMap      |
|   comparisonInverse := comparisonEquiv.symm.toContinuous...   |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Inverse laws                                                  |
|                                                              |
|   comparisonInverse.comp comparisonMap = id                   |
|   comparisonMap.comp comparisonInverse = id                   |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Source CCM24 row                                              |
|                                                              |
|   boundedComparisonMap                                        |
|   boundedComparisonInverse                                    |
|   boundedComparisonMapAndInverse                              |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Route post-Q tail comparison                                  |
|                                                              |
|   PostQSeriesTailBoundedComparison                            |
|   source_projection_order_endpoint_strip_normal_form          |
+--------------------------------------------------------------+
```

The old chain is too weak:

```text
Map Prop
  + Inverse Prop
  -> route tail comparison
```

The solved chain must preserve the shared owner:

```text
one comparisonEquiv
  -> comparisonMap and comparisonInverse
  -> inverse laws
  -> route tail comparison
```


## 5. What Counts As Solved

A6 solved means all items below hold in the same final snapshot.

```text
1. The active coordinate owner is not `Unit`.

2. The active coordinate owner proves the intended operator meaning:
     coordinateComparisonEquiv x = -x
     coordinateComparisonEquiv (coordinateComparisonEquiv x) = x
     coordinateComparisonEquiv.symm x = -x

3. The active Hilbert-side owner is one `SourceBoundedComparisonEquivData`
   value whose `comparisonMap` and `comparisonInverse` are derived from the
   same `comparisonEquiv`.

4. The source API exposes a combined theorem, not only two Props:
     boundedComparisonMap_and_inverse_of_data
   plus inverse-law readbacks for that same data.

5. `SourceSemilocalRows.sourceBoundedComparisonTraceClassTransport` and
   `SourceModelConstructorInput.sourceBoundedComparisonData` use the new owner.

6. `SourceBackedPostQBoundedComparisonData.ofExpandedSourcePackage` extracts
   one source data object from the expanded source package or from a new
   package/accessor field that preserves the
   `SourceModelConstructorInput.sourceBoundedComparisonModelData` owner for the
   source place. It stores both old route Props plus both inverse-law readbacks
   from that same object.

7. `post_q_series_tail_bounded_comparison_of_source_backed_data` is the active
   source-backed route theorem. The old
   `post_q_series_tail_bounded_comparison_of_source_backed` may remain only as
   compatibility and must call the data theorem or be marked compatibility-only.

8. The route-facing build and focused axiom audit pass in the WSL mirror.
```


## 6. What Does Not Count

Do not accept these shapes:

```text
Unit owner kept:
  abbrev SourceSignedCoordinateComparisonData ... := Unit

constructor filler kept:
  sourceBoundedComparisonModelData := by
    intro _ _
    exact ()

predicate pair only:
  boundedComparisonMap and boundedComparisonInverse appear separately in the
  route without a theorem tying both to one comparisonEquiv.

local theorem batch:
  comparisonMap_leftInverse passes audit, but PostQSeriesTailBoundedComparison
  still has only the old Prop pair.

endpoint package route:
  pkg.ccm24.sourceModel.soninComparison ... hFixed.2.2.2.2.1
  and hFixed.2.2.2.2.2 supply the route fields with no shared owner visible.

D-ignored operator family:
  def coordinateComparisonEquiv (_D : SourceSignedCoordinateComparisonData S H) :=
    (-1 : Real units) • ContinuousLinearEquiv.refl ...

  This proves facts about a namespace function, not about stored signed
  comparison data.

route wrapper only:
  post_q_series_tail_bounded_comparison_of_source_backed returns
    <map Prop, inverse Prop>
  without going through SourceBackedPostQBoundedComparisonData.
```

A6 can keep compatibility predicates. It cannot call the lane solved while the
active route path only sees those predicates.


## 7. Implementation Route

### Step A6.1: Pin Current Types

Run local type checks before editing:

```lean
#check SourceSupportWindowData.SourceSignedCoordinateComparisonData
#check SourceSupportWindowData.SourceBoundedComparisonCoordinateData
#check SourceSupportWindowData.SourceBoundedComparisonEquivData
#check SourceSupportWindowData.SourceBoundedComparisonData
#check SourceSupportWindowData.boundedComparisonMap
#check SourceSupportWindowData.boundedComparisonInverse
#check SourceSupportWindowData.boundedComparisonMap_and_inverse_of_data
#check SourceSemilocalRows.sourceBoundedComparisonMapData
#check SourceSemilocalRows.sourceBoundedComparisonInverseData
#check SourceSemilocalRows.sourceBoundedComparisonTraceClassTransport
#check SourceModelConstructorInput.sourceBoundedComparisonData
#check SourceConcreteBaseLayer.concreteRealSignedCoordinateComparisonData
#check SourceConcreteBaseLayer.concreteRealBoundedComparisonData
#check bounded_comparison_of_source_backed
#check PostQSeriesTailBoundedComparison
```

Expected result:

```text
The current signed coordinate owner checks as `Unit`. Treat that as the old
weak path.
```

### Step A6.2: Replace The Unit Signed Owner

Preferred shape:

```lean
structure SourceSignedCoordinateComparisonData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (_H : SourceCanonicalHilbertModelData S P V) where
  coordinateComparisonEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    P.placeCarrier V ≃L[ℝ] P.placeCarrier V
  coordinateComparisonEquiv_apply :
    forall x, coordinateComparisonEquiv x = -x
  coordinateComparisonEquiv_involutive :
    forall x, coordinateComparisonEquiv (coordinateComparisonEquiv x) = x
```

Lean syntax can differ. The content cannot differ.

Rejected replacement:

```text
structure SourceSignedCoordinateComparisonData where
  comparisonHolds : Prop
```

That only renames the old weak path.

The record fields must own the operator and laws. The accepted proof path must
not define `coordinateComparisonEquiv` as a namespace function that ignores
`D`.

### Step A6.3: Keep The Hilbert Equivalence As The Semantic Bridge

The key bridge should remain:

```text
SourceSignedCoordinateComparisonData.toEquivData
  -> SourceBoundedComparisonEquivData
```

It must transport the coordinate equivalence through:

```text
H.placeEquiv.trans (D.coordinateComparisonEquiv.trans H.placeEquiv.symm)
```

Then map/inverse facts must read from that one equivalence:

```text
comparisonMap := comparisonEquiv.toContinuousLinearMap
comparisonInverse := comparisonEquiv.symm.toContinuousLinearMap
comparisonInverse.comp comparisonMap = id
comparisonMap.comp comparisonInverse = id
```

Do not create separate map and inverse fields with no proof they are inverse.

### Step A6.4: Rewire Source Constructors

Update active constructors that currently fill the signed owner with `()`:

```text
SourceSemilocalRows.ofModelData
SourceSemilocalRows.ofIdentityFourierModelData
SourceModelConstructorInput.ofIdentityFourierModelData
concreteRealSignedCoordinateComparisonData
normalizedCoreSourceModelConstructorInputFromTheorems
```

The concrete provider should fill:

```text
coordinateComparisonEquiv := concreteRealCoordinateSignedComparisonEquiv
coordinateComparisonEquiv_apply := concreteRealCoordinateSignedComparisonEquiv_apply
coordinateComparisonEquiv_involutive :=
  concreteRealCoordinateSignedComparisonEquiv_involutive
```

If a constructor has only `SourceBoundedComparisonCoordinateData`, require a
conversion theorem into the signed owner or mark that constructor
compatibility-only.

### Step A6.5: Add The Source-Backed Route Data Owner

Current route shape:

```lean
def PostQSeriesTailBoundedComparison ... : Prop :=
  inputs.ccm24.boundedComparisonMap g.placeSet and
  inputs.ccm24.boundedComparisonInverse g.placeSet
```

Required stronger source-backed route shape:

```text
Route.SourceBackedPostQBoundedComparisonData pkg front
  carries one owner from the source package/accessor chain:
    sourceBoundedComparisonData
      := the SourceBoundedComparisonData object derived from
         SourceModelConstructorInput.sourceBoundedComparisonModelData
         at the source-backed placeSet and canonical Hilbert model

  derives old route Props:
    boundedComparisonMap :
      inputs.ccm24.boundedComparisonMap g.placeSet
    boundedComparisonInverse :
      inputs.ccm24.boundedComparisonInverse g.placeSet

  carries inverse-law readbacks from the same owner:
    comparisonMap_leftInverse_apply
    comparisonMap_rightInverse_apply

PostQSeriesTailBoundedComparison
  is derived from SourceBackedPostQBoundedComparisonData for compatibility.
```

Concrete declaration names to add:

```text
SourceObject.CCM24SemilocalObjectPackage.sourceBackedBoundedComparisonData
  or the smallest equivalent accessor that keeps the dependent source data
  object alive through package construction

SourceBackedPostQBoundedComparisonData
SourceBackedPostQBoundedComparisonData.ofExpandedSourcePackage
post_q_series_tail_bounded_comparison_of_source_backed_data
```

Required old-path deletion/demotion:

```text
SourceBackedFixedSTest.ofExpandedSourcePackage must not derive the active A6
tail evidence only from:
  hFixed.2.2.2.2.1
  hFixed.2.2.2.2.2

Those projections may remain only as compatibility output from
SourceBackedPostQBoundedComparisonData.
```

The old theorem may remain:

```text
post_q_series_tail_bounded_comparison_of_source_backed
```

but it must become a compatibility wrapper over
`post_q_series_tail_bounded_comparison_of_source_backed_data`, or the final
report must mark A6 partial.

If this source-backed owner is too narrow for a later generic route theorem,
write a separate route API plan. Do not broaden A6 by inventing a free
`SemilocalModelSymbols.boundedComparisonData : PlaceSet -> Prop` field; that
would only rename the old Prop pair.

If changing the source-backed route surface is too broad for the batch, the
plan can still accept a source-side A6 partial cut only when the final report
says:

```text
A6 partial:
  source bounded comparison owner is non-vacuous and audited,
  but route tail comparison still consumes only old predicates.
```

Do not call that solved.


## 8. Static Rejection Scans

Run before and after implementation:

```text
rg -n "abbrev SourceSignedCoordinateComparisonData|SourceSignedCoordinateComparisonData.*:=\\s*Unit" ConnesWeilRH/Source -g "*.lean"

rg -n "sourceBoundedComparisonModelData := by|concreteRealSignedCoordinateComparisonData.*:=|exact \\(\\)" ConnesWeilRH/Source ConnesWeilRH/Dev -g "*.lean"

rg -n "boundedComparisonMap := by|boundedComparisonInverse := by|bounded_comparison_of_source_backed|PostQSeriesTailBoundedComparison" ConnesWeilRH/Route ConnesWeilRH/Source -g "*.lean"

rg -n "_D : SourceSignedCoordinateComparisonData|\\(_D : SourceSignedCoordinateComparisonData|exact .*ContinuousLinearEquiv\\.refl|exact .* • ContinuousLinearEquiv\\.refl|PostQSeriesTailBoundedComparison inputs g lambda :=|post_q_series_tail_bounded_comparison_of_source_backed\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "sourceBackedBoundedComparisonData|SourceBackedPostQBoundedComparisonData|post_q_series_tail_bounded_comparison_of_source_backed_data" ConnesWeilRH/Route ConnesWeilRH/Source -g "*.lean"

rg -n "comparisonMap_leftInverse|comparisonMap_rightInverse|comparisonMap_leftInverse_apply|comparisonMap_rightInverse_apply|coordinateComparisonEquiv_involutive|coordinateComparisonEquiv_comp_self" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "SourceSignedCoordinateComparisonData.*Prop|boundedComparison.*Prop|Set\\.univ|\\bTrue\\b|\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"
```

Acceptance reading:

```text
1. No active `SourceSignedCoordinateComparisonData := Unit` remains.

2. No active bounded-comparison constructor fills the lane with `exact ()`.

3. Remaining old predicate-pair route uses must be documented as compatibility
   or marked as the remaining boundary.

4. The source-backed route path must contain
   `sourceBackedBoundedComparisonData`,
   `SourceBackedPostQBoundedComparisonData`, and
   `post_q_series_tail_bounded_comparison_of_source_backed_data`.

5. No active semantic theorem may get its operator from an ignored
   `SourceSignedCoordinateComparisonData` parameter. Remaining
   ignored-parameter hits must be compatibility-only and outside the accepted
   A6 path.

6. No new `sorry`, `admit`, project axiom, `constant`, `opaque`, `unsafe`,
   `True`, or `Set.univ` may appear in the A6 lane.
```


## 9. WSL Build Gate

Sync first:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'
```

Run the smallest route-facing build gate:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.AnalyticSourceModel ConnesWeilRH.Source.CCM24SourceModel ConnesWeilRH.Route.RouteTheorem'
```

If `ConnesWeilRH/Dev/UnconditionalSkeleton.lean` changes, run:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean'
```

Passing Source builds alone does not close A6 because A6 has route-facing
post-Q tail and sign-defect consumers.


## 10. Focused Axiom Audit

Create a scratch file in the WSL mirror that imports the owner modules and
checks the semantic targets:

```lean
import ConnesWeilRH.Source.AnalyticSourceModel
import ConnesWeilRH.Source.CCM24SourceModel
import ConnesWeilRH.Route.RouteTheorem

open ConnesWeilRH
open ConnesWeilRH.Source
open ConnesWeilRH.Source.AnalyticCore
open ConnesWeilRH.Route

#check SourceSupportWindowData.SourceSignedCoordinateComparisonData

#check SourceSupportWindowData.SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_apply
#print axioms SourceSupportWindowData.SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_apply

#check SourceSupportWindowData.SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_involutive
#print axioms SourceSupportWindowData.SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_involutive

#check SourceSupportWindowData.SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_symm_apply
#print axioms SourceSupportWindowData.SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_symm_apply

#check SourceSupportWindowData.SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_comp_self
#print axioms SourceSupportWindowData.SourceSignedCoordinateComparisonData.coordinateComparisonEquiv_comp_self

#check SourceSupportWindowData.SourceSignedCoordinateComparisonData.toEquivData
#print axioms SourceSupportWindowData.SourceSignedCoordinateComparisonData.toEquivData

#check SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap
#print axioms SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap

#check SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonInverse
#print axioms SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonInverse

#check SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap_leftInverse
#print axioms SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap_leftInverse

#check SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap_rightInverse
#print axioms SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap_rightInverse

#check SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap_leftInverse_apply
#print axioms SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap_leftInverse_apply

#check SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap_rightInverse_apply
#print axioms SourceSupportWindowData.SourceBoundedComparisonEquivData.comparisonMap_rightInverse_apply

#check SourceSupportWindowData.SourceBoundedComparisonData.comparisonMap_leftInverse_apply_of_data
#print axioms SourceSupportWindowData.SourceBoundedComparisonData.comparisonMap_leftInverse_apply_of_data

#check SourceSupportWindowData.SourceBoundedComparisonData.comparisonMap_rightInverse_apply_of_data
#print axioms SourceSupportWindowData.SourceBoundedComparisonData.comparisonMap_rightInverse_apply_of_data

#check SourceSupportWindowData.boundedComparisonMap_and_inverse_of_data
#print axioms SourceSupportWindowData.boundedComparisonMap_and_inverse_of_data

#check SourceSemilocalRows.sourceBoundedComparisonMapData
#print axioms SourceSemilocalRows.sourceBoundedComparisonMapData

#check SourceSemilocalRows.sourceBoundedComparisonInverseData
#print axioms SourceSemilocalRows.sourceBoundedComparisonInverseData

#check SourceSemilocalRows.sourceBoundedComparisonTraceClassTransport
#print axioms SourceSemilocalRows.sourceBoundedComparisonTraceClassTransport

#check SourceModelConstructorInput.sourceBoundedComparisonData
#print axioms SourceModelConstructorInput.sourceBoundedComparisonData

#check SourceConcreteBaseLayer.concreteRealSignedCoordinateComparisonData
#print axioms SourceConcreteBaseLayer.concreteRealSignedCoordinateComparisonData

#check SourceConcreteBaseLayer.concreteRealBoundedComparisonData
#print axioms SourceConcreteBaseLayer.concreteRealBoundedComparisonData

#check SourceConcreteBaseLayer.concreteRealBoundedComparisonMap
#print axioms SourceConcreteBaseLayer.concreteRealBoundedComparisonMap

#check SourceConcreteBaseLayer.concreteRealBoundedComparisonInverse
#print axioms SourceConcreteBaseLayer.concreteRealBoundedComparisonInverse

#check SourceObject.CCM24SemilocalObjectPackage.sourceBackedBoundedComparisonData
#print axioms SourceObject.CCM24SemilocalObjectPackage.sourceBackedBoundedComparisonData

#check SourceBackedPostQBoundedComparisonData.ofExpandedSourcePackage
#print axioms SourceBackedPostQBoundedComparisonData.ofExpandedSourcePackage

#check post_q_series_tail_bounded_comparison_of_source_backed_data
#print axioms post_q_series_tail_bounded_comparison_of_source_backed_data

#check bounded_comparison_of_source_backed
#print axioms bounded_comparison_of_source_backed

#check post_q_series_tail_bounded_comparison_of_source_backed
#print axioms post_q_series_tail_bounded_comparison_of_source_backed
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local axiom
constant
opaque
unsafe
free Prop field that states bounded comparison
endpoint package theorem
certificate atom
```

Do not audit only `boundedComparisonMap` and `boundedComparisonInverse`. Audit
the shared equivalence and both inverse laws.


## 11. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  SourceSignedCoordinateComparisonData is no longer Unit on the active A6 path.
  Active bounded-comparison constructors no longer fill the lane with
  `exact ()`.
  Route tail comparison no longer depends only on independent map/inverse
  Props.
  Active coordinateComparisonEquiv theorems no longer ignore the
  SourceSignedCoordinateComparisonData record argument.

New semantic owner:
  <exact declaration>

Semantic theorem:
  <exact theorem proving coordinateComparisonEquiv x = -x>
  <exact theorem proving coordinateComparisonEquiv is involutive>
  <exact theorem proving comparisonInverse.comp comparisonMap = id>
  <exact theorem proving comparisonMap.comp comparisonInverse = id>

Consumer rewires:
  SourceSemilocalRows.sourceBoundedComparisonModelData
  SourceSemilocalRows.sourceBoundedComparisonMapData
  SourceSemilocalRows.sourceBoundedComparisonInverseData
  SourceSemilocalRows.sourceBoundedComparisonTraceClassTransport
  SourceModelConstructorInput.sourceBoundedComparisonModelData
  SourceModelConstructorInput.sourceBoundedComparisonData
  SourceObject.CCM24SemilocalObjectPackage.sourceBackedBoundedComparisonData
  SourceBackedFixedSTest.ofExpandedSourcePackage
  SourceBackedPostQBoundedComparisonData.ofExpandedSourcePackage
  post_q_series_tail_bounded_comparison_of_source_backed_data
  bounded_comparison_of_source_backed
  PostQSeriesTailBoundedComparison

Semantic sufficiency:
  Bounded comparison reaches the post-Q route tail as one comparison
  equivalence with inverse laws. This is strong enough for the next route step
  because route sign-defect transport can rely on a linked map/inverse pair,
  not two unrelated Prop witnesses.

Build:
  <exact WSL command>
  <result>

Focused axiom audit:
  <theorem list>
  <axiom output>

Remaining black box:
  <exact declaration/type, if any>
```


## 12. Stop Rule

Stop and mark A6 partial if the only buildable route leaves:

```text
PostQSeriesTailBoundedComparison inputs g lambda :=
  inputs.ccm24.boundedComparisonMap g.placeSet and
  inputs.ccm24.boundedComparisonInverse g.placeSet
```

as the active route evidence.

Stop and mark A6 diagnostic-only if a correct route fix needs a new public
route record outside the current CCM24 source/window/model slice.

Do not weaken bounded comparison with `True`, `Set.univ`, a free `Prop`, or an
endpoint package theorem.
