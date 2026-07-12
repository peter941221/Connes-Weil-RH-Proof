# A5 Scaling Action Semantics Hard-Gate Plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane A5.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

A5 is solved only if the active CCM24 source-to-route path gets a non-vacuous
scaling action owner. A proof that `scalingActionImplemented` has a witness is
not enough while the active owner is `Unit`.

```text
old weak path:
  SourceScalarCoordinateScalingData S H := Unit
    -> sourceScalingActionModelData V H := ()
    -> scalingActionImplemented_of_scalar_coordinate_data
    -> inputs.ccm24.scalingActionImplemented placeSet
    -> SourceBackedFixedSTest.ofExpandedSourcePackage
    -> canonical_model_compatibility_of_source_backed

new semantic owner/API:
  SourceScalarCoordinateScalingData must be a real structure, not an abbrev
  or namespace-defined operator family. It carries:
    coordinateScaleEquiv
    coordinateScaleEquiv_one
    coordinateScaleEquiv_mul
    coordinateScaleAction
    coordinateScaleAction_units
    coordinateScaleAction_one
    coordinateScaleAction_mul
    coordinateScaleAction_apply
    coordinateScaleEquiv_apply

  SourceConcreteBaseLayer.concreteRealScalarCoordinateScalingData must fill
  that structure from concrete scalar multiplication operators and laws.

real consumer rewired:
  SourceSemilocalRows.sourceScalingActionModelData
  SourceSemilocalRows.sourceScalingActionData
  SourceModelConstructorInput.sourceScalingActionModelData
  SourceModelConstructorInput.sourceScalingActionData
  concreteRealScalingActionImplemented
  SourceBackedFixedSTest.ofExpandedSourcePackage
  canonical_model_compatibility_of_source_backed

same-object alias / wrapper rejection scan:
  rg -n "abbrev SourceScalarCoordinateScalingData|SourceScalarCoordinateScalingData.*:=\\s*Unit|sourceScalingActionModelData := by|exact \\(\\)|scalingActionImplemented_of_scalar_coordinate_data|scalingActionImplemented_of_data|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"

field-use rejection scan:
  rg -n "_D : SourceScalarCoordinateScalingData|\\(_D : SourceScalarCoordinateScalingData|exact .*ContinuousLinear(Map|Equiv)\\.(id|refl)|exact .* • ContinuousLinear(Map|Equiv)\\.(id|refl)" ConnesWeilRH/Source -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.AnalyticSourceModel \
    ConnesWeilRH.Source.CCM24SourceModel \
    ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  SourceScalarCoordinateScalingData.coordinateScaleEquiv_apply
  SourceScalarCoordinateScalingData.coordinateScaleAction_apply
  SourceScalarCoordinateScalingData.coordinateScaleEquiv_one
  SourceScalarCoordinateScalingData.coordinateScaleEquiv_mul
  SourceScalarCoordinateScalingData.coordinateScaleAction_units
  SourceScalarCoordinateScalingData.coordinateScaleAction_one
  SourceScalarCoordinateScalingData.coordinateScaleAction_mul
  SourceScalarCoordinateScalingData.toScalingCoordinateActionData
  SourceScalingCoordinateActionData.toScalingActionData
  SourceSupportWindowData.scalingActionImplemented
  SourceSupportWindowData.scalingActionImplemented_of_scalar_coordinate_data
  SourceSemilocalRows.sourceScalingActionData
  SourceModelConstructorInput.sourceScalingActionData
  SourceConcreteBaseLayer.concreteRealCoordinateScaleEquiv_one
  SourceConcreteBaseLayer.concreteRealCoordinateScaleEquiv_mul
  SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_units
  SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_one
  SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_mul
  SourceConcreteBaseLayer.concreteRealScalarCoordinateScalingData
  SourceConcreteBaseLayer.concreteRealScalingActionImplemented
  canonical_model_compatibility_of_source_backed

semantic sufficiency for next route/RH step:
  Route-side canonical compatibility must no longer receive scaling as an
  existential proof over `Unit`. It must receive a source-local scaling owner
  whose coordinate operator is scalar multiplication on the concrete place
  carrier and whose multiplicative laws feed the old
  `scalingActionImplemented` predicate.
```

Rejected as not solved:

```text
1. The patch leaves:
     abbrev SourceScalarCoordinateScalingData ... := Unit
   as the active owner.

2. The patch only adds wrapper theorems around:
     scalingActionImplemented_of_scalar_coordinate_data

3. The patch keeps active constructors filling:
     sourceScalingActionModelData := by intro _ _; exact ()

4. The patch proves `coordinateScaleAction_mul` for concrete functions but
   leaves route-facing canonical compatibility on the old existential row.

5. The patch changes the public API but still lets `scalingActionImplemented`
   mean "there exists a `Unit` witness".

6. The patch replaces `Unit` with a structure but keeps the active semantic
   operators as namespace definitions that ignore the record argument.
```


## 2. Result First

Expected result:

```text
Good only if:
  A5 replaces the active `Unit` scaling witness with a concrete scalar
  coordinate scaling owner and rewires source/route consumers to it.

Partial only if:
  A5 adds or audits scalar multiplication facts but leaves the active route
  consumer on `Unit`.

Rejected if:
  A5 only renames `Unit`, adds a compatibility wrapper, or treats clean axiom
  output for `scalingActionImplemented` as semantic completion.
```

A5 is not a request for more local theorems about `ContinuousLinearMap.smul`.
A5 is a request to remove the empty scaling owner from the active RH route.


## 3. Current Evidence

Ledger source:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:99-104
  A5. scaling action semantics
    SourceScalingCoordinateActionData
    SourceScalarCoordinateScalingData
    multiplicative scaling law
    arbitrary-place compatibility
```

Project memory already warns against stale scaling work:

```text
MEMORY.md
  The active owner is now:
    SourceScalarCoordinateScalingData

  The old SourceScalingActionData and SourceScalingCoordinateActionData
  surfaces are compatibility only.

  Future scaling progress must drill below adjacent source owners or remove a
  different real old consumer path.
```

Current weak owner:

```text
ConnesWeilRH/Source/AnalyticCore.lean:1229-1233
  abbrev SourceScalarCoordinateScalingData ... := Unit
```

Current predicate:

```text
ConnesWeilRH/Source/AnalyticCore.lean:2074-2080
  def scalingActionImplemented S V : Prop :=
    exists P H, Nonempty (SourceScalarCoordinateScalingData S H)
```

Current active source rows:

```text
ConnesWeilRH/Source/AnalyticCore.lean:5199-5204
  SourceSemilocalRows.sourceScalingActionModelData :
    forall V H, SourceScalarCoordinateScalingData S H

ConnesWeilRH/Source/AnalyticCore.lean:5363-5371
  SourceSemilocalRows.sourceScalingActionData uses
    scalingActionImplemented_of_scalar_coordinate_data
```

Current route consumer:

```text
ConnesWeilRH/Route/Definitions.lean:132-133
  SourceBackedFixedSTest.scalingActionImplemented :
    inputs.ccm24.scalingActionImplemented placeSet

ConnesWeilRH/Route/Definitions.lean:191-195
  SourceBackedFixedSTest.ofExpandedSourcePackage derives the row from
    pkg.ccm24.sourceModel.soninComparison ... hFixed.2.2.1

ConnesWeilRH/Route/AdmissibleWindow.lean:96-100
  canonical_model_compatibility_of_source_backed returns:
    scalingActionImplemented and fourierGradingCompatible
```

Concrete scalar-map facts exist:

```text
ConnesWeilRH/Source/AnalyticCore.lean:5650-5745
  concreteRealCoordinateScaleEquiv_one
  concreteRealCoordinateScaleEquiv_mul
  concreteRealCoordinateScaleAction_units
  concreteRealCoordinateScaleAction_one
  concreteRealCoordinateScaleAction_mul

ConnesWeilRH/Source/AnalyticCore.lean:5764-5774
  concreteRealScalarCoordinateScalingData := ()
```

The evidence says scalar multiplication lemmas exist. The gap is that the
active semantic owner stores none of them.


## 4. First-Principles Dependency Chain

```text
+--------------------------------------------------------------+
| Concrete place carrier                                        |
|                                                              |
|   P.placeCarrier V                                           |
|   concrete carrier currently Real                             |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Scalar coordinate action                                      |
|                                                              |
|   u : Real units  ->  x |-> (u : Real) • x                    |
|   a : Real        ->  x |-> a • x                             |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Multiplicative laws                                           |
|                                                              |
|   scaleEquiv 1 = refl                                        |
|   scaleEquiv (a * b) = scaleEquiv a trans scaleEquiv b        |
|   scaleAction 1 = id                                         |
|   scaleAction (a * b) = scaleAction a comp scaleAction b      |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Source predicate compatibility                                |
|                                                              |
|   scalingActionImplemented V                                 |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Route canonical compatibility                                 |
|                                                              |
|   canonical_model_compatibility_of_source_backed              |
+--------------------------------------------------------------+
```

The old chain skips the middle:

```text
Unit witness
  -> Nonempty Unit
  -> scalingActionImplemented
  -> route canonical compatibility
```

The hard gate forces the middle boxes to carry data and laws.


## 5. What Counts As Solved

A5 solved means all items below hold in the same final snapshot.

```text
1. `SourceScalarCoordinateScalingData` is no longer definitionally `Unit` on
   the active path.

2. The active scaling owner stores the coordinate operator and laws as record
   fields:
     coordinateScaleEquiv
     coordinateScaleEquiv_one
     coordinateScaleEquiv_mul
     coordinateScaleAction
     coordinateScaleAction_units
     coordinateScaleAction_one
     coordinateScaleAction_mul

3. The readback theorems named below either project those record fields or
   prove facts from the concrete record instance. They must not define the
   operator by ignoring `D`.

4. Concrete data fills that owner from:
     concreteRealCoordinateScaleEquiv
     concreteRealCoordinateScaleAction
   and the existing concrete one/mul/unit theorems.

5. `SourceSemilocalRows.sourceScalingActionData` derives
   `scalingActionImplemented` from the concrete semantic owner, not from a
   `Unit` witness.

6. `SourceModelConstructorInput.sourceScalingActionData` follows the same
   semantic path.

7. `SourceBackedFixedSTest.ofExpandedSourcePackage` and
   `canonical_model_compatibility_of_source_backed` remain type-correct after
   the old `Unit` path disappears from the active proof.

8. The route-facing build and focused axiom audit pass in the WSL mirror.
```


## 6. What Does Not Count

Do not accept these shapes:

```text
Unit owner kept:
  abbrev SourceScalarCoordinateScalingData ... := Unit

constructor filler kept:
  sourceScalingActionModelData := by
    intro _ _
    exact ()

predicate wrapper:
  new_scalingActionImplemented := old_scalingActionImplemented

compatibility-only migration:
  SourceScalingCoordinateActionData -> SourceScalingActionData
  with no active route/source consumer leaving the `Unit` owner

local theorem batch:
  concreteRealCoordinateScaleAction_mul passes audit, but
  SourceBackedFixedSTest still consumes an existential `Unit` witness

D-ignored operator family:
  def coordinateScaleAction (_D : SourceScalarCoordinateScalingData S H) a :=
    a • ContinuousLinearMap.id ...

  This proves facts about a namespace function, not about stored scaling data.
```

Clean axiom output for the old predicate proves trust. It does not prove A5 has
semantic content.


## 7. Implementation Route

### Step A5.1: Pin Current Types

Run local type checks before editing:

```lean
#check SourceSupportWindowData.SourceScalarCoordinateScalingData
#check SourceSupportWindowData.SourceScalingCoordinateActionData
#check SourceSupportWindowData.SourceScalingActionData
#check SourceSupportWindowData.scalingActionImplemented
#check SourceSupportWindowData.scalingActionImplemented_of_scalar_coordinate_data
#check SourceSemilocalRows.sourceScalingActionData
#check SourceModelConstructorInput.sourceScalingActionData
#check SourceConcreteBaseLayer.concreteRealCoordinateScaleEquiv
#check SourceConcreteBaseLayer.concreteRealCoordinateScaleAction
#check SourceConcreteBaseLayer.concreteRealScalarCoordinateScalingData
#check SourceConcreteBaseLayer.concreteRealScalingActionImplemented
```

Expected result:

```text
The current owner checks as `Unit`. Treat that as the old weak path, not as
accepted scaling semantics.
```

### Step A5.2: Replace The Unit Owner With A Record

Preferred shape:

```lean
structure SourceScalarCoordinateScalingData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (_H : SourceCanonicalHilbertModelData S P V) where
  coordinateScaleEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ℝˣ → P.placeCarrier V ≃L[ℝ] P.placeCarrier V
  coordinateScaleEquiv_one :
    ...
  coordinateScaleEquiv_mul :
    ...
  coordinateScaleAction :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ℝ → P.placeCarrier V →L[ℝ] P.placeCarrier V
  coordinateScaleAction_units :
    ...
  coordinateScaleAction_one :
    ...
  coordinateScaleAction_mul :
    ...
```

Use the current `SourceScalingCoordinateActionData` fields as the exact type
source. Do not make the new record a free `Prop` package.

### Step A5.3: Move Existing Scalar Theorems Onto The Record

Keep these theorem names or provide compatibility aliases:

```text
SourceScalarCoordinateScalingData.coordinateScaleEquiv_apply
SourceScalarCoordinateScalingData.coordinateScaleAction_apply
SourceScalarCoordinateScalingData.coordinateScaleEquiv_one
SourceScalarCoordinateScalingData.coordinateScaleEquiv_mul
SourceScalarCoordinateScalingData.coordinateScaleAction_units
SourceScalarCoordinateScalingData.coordinateScaleAction_one
SourceScalarCoordinateScalingData.coordinateScaleAction_mul
```

After the migration, the proofs must project record fields or prove pointwise
scalar multiplication facts from the concrete record instance. They must not
use `()` as evidence, and they must not define `coordinateScaleEquiv` or
`coordinateScaleAction` as namespace functions that ignore `D`.

### Step A5.4: Rebuild Compatibility Bridges

These compatibility surfaces can remain, but they must derive from the new
record:

```text
SourceScalarCoordinateScalingData.toScalingCoordinateActionData
SourceScalingCoordinateActionData.toScalingActionData
SourceSupportWindowData.scalingActionImplemented_of_scalar_coordinate_data
SourceSupportWindowData.scalingActionImplemented_of_data
```

Allowed compatibility path:

```text
new scalar coordinate record
  -> SourceScalingCoordinateActionData
  -> SourceScalingActionData
```

Rejected compatibility path:

```text
Unit
  -> SourceScalingCoordinateActionData
  -> SourceScalingActionData
```

### Step A5.5: Rewire Source Constructors

Update constructors that now fill scaling with `()`:

```text
SourceSemilocalRows.ofModelData
SourceSemilocalRows.ofIdentityFourierModelData
SourceModelConstructorInput.ofIdentityFourierModelData
concreteRealScalarCoordinateScalingData
normalizedCoreSourceModelConstructorInputFromTheorems
```

If an older constructor accepts `SourceScalingCoordinateActionData`, either:

```text
1. change it to accept SourceScalarCoordinateScalingData directly; or
2. require a theorem that converts coordinate-action data into the new scalar
   owner without losing scalar multiplication semantics.
```

Do not silently fill the new record with arbitrary identity operators unless
the concrete place carrier theorem proves that identity is the intended scalar
action for all parameters. For scalar action, the expected concrete operator is
`a • x`, not identity for every `a`.

### Step A5.6: Rewire Route-Facing Evidence

The route field may keep this external type:

```lean
inputs.ccm24.scalingActionImplemented placeSet
```

But its proof path must go through the new owner:

```text
SourceBackedFixedSTest.ofExpandedSourcePackage
  -> SourceModelConstructorInput.sourceScalingActionData
  -> SourceSemilocalRows.sourceScalingActionData
  -> scalingActionImplemented_of_scalar_coordinate_data
  -> non-vacuous SourceScalarCoordinateScalingData
```

If route consumers still receive only the old existential row, the final report
must say A5 is partial.


## 8. Static Rejection Scans

Run before and after implementation:

```text
rg -n "abbrev SourceScalarCoordinateScalingData|SourceScalarCoordinateScalingData.*:=\\s*Unit" ConnesWeilRH/Source -g "*.lean"

rg -n "sourceScalingActionModelData := by|exact \\(\\)" ConnesWeilRH/Source ConnesWeilRH/Dev -g "*.lean"

rg -n "scalingActionImplemented_of_scalar_coordinate_data|scalingActionImplemented_of_data|sourceScalingActionData|concreteRealScalingActionImplemented" ConnesWeilRH/Source ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"

rg -n "coordinateScaleEquiv|coordinateScaleAction|concreteRealCoordinateScaleEquiv|concreteRealCoordinateScaleAction|smul_smul|ContinuousLinearMap\\.id" ConnesWeilRH/Source/AnalyticCore.lean

rg -n "_D : SourceScalarCoordinateScalingData|\\(_D : SourceScalarCoordinateScalingData|exact .*ContinuousLinear(Map|Equiv)\\.(id|refl)|exact .* • ContinuousLinear(Map|Equiv)\\.(id|refl)" ConnesWeilRH/Source -g "*.lean"

rg -n "SourceScalarCoordinateScalingData.*Prop|scalingAction.*Prop|Set\\.univ|\\bTrue\\b|\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"
```

Acceptance reading:

```text
1. No active `SourceScalarCoordinateScalingData := Unit` remains.

2. No active constructor fills scaling with `exact ()`.

3. Any remaining `exact ()` hit must be outside A5 or documented as an old
   compatibility path that no route/source A5 consumer uses.

4. No new `sorry`, `admit`, project axiom, `constant`, `opaque`, `unsafe`,
   `True`, or `Set.univ` may appear in the A5 lane.

5. No active semantic theorem may get its operator from an ignored
   `SourceScalarCoordinateScalingData` parameter. Remaining ignored-parameter
   hits must be compatibility-only and outside the accepted A5 path.
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

Passing `ConnesWeilRH.Source.AnalyticCore` alone does not close A5 because A5
has a route-facing canonical-compatibility consumer.


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

#check SourceSupportWindowData.SourceScalarCoordinateScalingData

#check SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleEquiv_apply
#print axioms SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleEquiv_apply

#check SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleAction_apply
#print axioms SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleAction_apply

#check SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleEquiv_one
#print axioms SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleEquiv_one

#check SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleEquiv_mul
#print axioms SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleEquiv_mul

#check SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleAction_units
#print axioms SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleAction_units

#check SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleAction_one
#print axioms SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleAction_one

#check SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleAction_mul
#print axioms SourceSupportWindowData.SourceScalarCoordinateScalingData.coordinateScaleAction_mul

#check SourceSupportWindowData.SourceScalarCoordinateScalingData.toScalingCoordinateActionData
#print axioms SourceSupportWindowData.SourceScalarCoordinateScalingData.toScalingCoordinateActionData

#check SourceSupportWindowData.SourceScalingCoordinateActionData.toScalingActionData
#print axioms SourceSupportWindowData.SourceScalingCoordinateActionData.toScalingActionData

#check SourceSupportWindowData.scalingActionImplemented
#print axioms SourceSupportWindowData.scalingActionImplemented

#check SourceSupportWindowData.scalingActionImplemented_of_scalar_coordinate_data
#print axioms SourceSupportWindowData.scalingActionImplemented_of_scalar_coordinate_data

#check SourceSemilocalRows.sourceScalingActionData
#print axioms SourceSemilocalRows.sourceScalingActionData

#check SourceModelConstructorInput.sourceScalingActionData
#print axioms SourceModelConstructorInput.sourceScalingActionData

#check SourceConcreteBaseLayer.concreteRealCoordinateScaleEquiv_one
#print axioms SourceConcreteBaseLayer.concreteRealCoordinateScaleEquiv_one

#check SourceConcreteBaseLayer.concreteRealCoordinateScaleEquiv_mul
#print axioms SourceConcreteBaseLayer.concreteRealCoordinateScaleEquiv_mul

#check SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_units
#print axioms SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_units

#check SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_one
#print axioms SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_one

#check SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_mul
#print axioms SourceConcreteBaseLayer.concreteRealCoordinateScaleAction_mul

#check SourceConcreteBaseLayer.concreteRealScalarCoordinateScalingData
#print axioms SourceConcreteBaseLayer.concreteRealScalarCoordinateScalingData

#check SourceConcreteBaseLayer.concreteRealScalingActionImplemented
#print axioms SourceConcreteBaseLayer.concreteRealScalingActionImplemented

#check canonical_model_compatibility_of_source_backed
#print axioms canonical_model_compatibility_of_source_backed
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
free Prop field that states scaling
endpoint package theorem
certificate atom
```

Do not audit only `scalingActionImplemented`. Audit the concrete scalar action
laws and the route-facing consumer.


## 11. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  SourceScalarCoordinateScalingData is no longer Unit on the active A5 path.
  Active constructors no longer fill scaling with `exact ()`.
  Active coordinateScaleEquiv / coordinateScaleAction theorems no longer ignore
  the SourceScalarCoordinateScalingData record argument.

New semantic owner:
  <exact declaration>

Semantic theorem:
  <exact theorem proving coordinateScaleAction a x = a • x>
  <exact theorem proving coordinateScaleAction (a * b) =
    coordinateScaleAction a comp coordinateScaleAction b>
  <exact theorem proving coordinateScaleEquiv (u * v) =
    coordinateScaleEquiv u trans coordinateScaleEquiv v>

Consumer rewires:
  SourceSemilocalRows.sourceScalingActionModelData
  SourceSemilocalRows.sourceScalingActionData
  SourceModelConstructorInput.sourceScalingActionModelData
  SourceModelConstructorInput.sourceScalingActionData
  concreteRealScalingActionImplemented
  SourceBackedFixedSTest.ofExpandedSourcePackage
  canonical_model_compatibility_of_source_backed

Semantic sufficiency:
  Scaling reaches the route as concrete scalar-coordinate action semantics,
  not as an existential Unit witness. This is strong enough for the next
  route/source step because canonical compatibility can now depend on actual
  scalar multiplication laws on the source place carrier.

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

Stop and mark A5 partial if the only buildable route leaves this active:

```text
SourceScalarCoordinateScalingData := Unit
```

Stop and mark A5 diagnostic-only if the fix needs a new mathematical scaling
model outside the current CCM24 source/window/model slice.

Do not weaken the route by replacing scaling with `True`, `Set.univ`, a free
`Prop`, or an endpoint package theorem.
