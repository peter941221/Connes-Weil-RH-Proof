# CCM24 Fourier Transform / Grading Semantics Plan

Date: 2026-07-06

Status: planning artifact only.  This document is not accepted Lean progress and
does not claim an unconditional proof of `_root_.RiemannHypothesis`.


## 1. Problem Restatement

Peter wants the CCM24 Fourier transform / grading semantics lane attacked next.

The concrete question is not:

```text
Can we add more Fourier readback lemmas?
```

The real question is:

```text
Can the active CCM24 Fourier grading path stop being only an identity/line-span
provider, and instead be owned by a named source-local Fourier semantics model
that connects:

  concrete Fourier transform semantics
      -> coordinate Fourier equivalence
      -> grade-subspace preservation
      -> SourceSemilocalRows / SourceModelConstructorInput consumers
```


## 2. Evidence From Current Project State

Current local rules:

```text
AGENTS.md:
  2026-07-06 Peter paused subagent usage.
  Work single-agent by default.
  Accepted Lean batches must be rechecked in the main WSL mirror.
```

Current Fourier grading owner in source code:

```text
ConnesWeilRH/Source/AnalyticCore.lean:
  SourceFourierGradingData stores:
    gradeIndex
    gradeSubspace : gradeIndex -> Submodule Real H.hilbertCarrier
    fourierEquiv : H.hilbertCarrier ≃L[Real] H.hilbertCarrier
    fourier_preserves_grade
```

Current coordinate layer:

```text
ConnesWeilRH/Source/AnalyticCore.lean:
  SourceFourierCoordinateGradingData stores:
    coordinateGradeIndex
    coordinateGradeSubspace
    coordinateFourierEquiv
    coordinateFourier_preserves_grade

  SourceIdentityFourierCoordinateGradingData stores only:
    coordinateGradeIndex
    coordinateGradeSubspace

  SourceLineFourierCoordinateGradingData := Unit
```

Current active CCM24 constructor path:

```text
ConnesWeilRH/Source/AnalyticCore.lean
ConnesWeilRH/Source/AnalyticSourceModel.lean

  SourceSemilocalRows.sourceFourierGradingModelData :
    forall V H,
      SourceLineFourierCoordinateGradingData S (P := sourcePlaceCarrierData) V

  SourceModelConstructorInput.sourceFourierGradingModelData :
    forall V H,
      SourceLineFourierCoordinateGradingData core.supportWindow
        (P := sourcePlaceCarrierData) V

  SourceSemilocalRows.ofLineFourierModelData
  SourceModelConstructorInput.ofLineFourierModelData
```

Latest accepted memory:

```text
MEMORY.md:
  Active consumers no longer require arbitrary
  SourceIdentityFourierCoordinateGradingData for Fourier grading.

  New lower owner:
    SourceLineFourierCoordinateGradingData

  Fourier grading lane no longer stops at arbitrary grade-subspace data.
```

Important mismatch to respect:

```text
Older AGENTS.md text names the frontier as:
  SourceFourierGradingData.fourierOperator : H.hilbertCarrier ->L[Real] H.hilbertCarrier

Current source has:
  SourceFourierGradingData.fourierEquiv : H.hilbertCarrier ≃L[Real] H.hilbertCarrier

Plan must follow current source, not the older field wording.
```


## 3. First-Principles Decomposition

The semantic chain should have four independent layers:

```text
+---------------------------------------------------------------+
| Layer A: concrete transform semantics                         |
|                                                               |
|   What is the Fourier transform on the concrete carrier?       |
|   What operator/equivalence represents it in Lean?             |
+-------------------------------+-------------------------------+
                                |
                                v
+---------------------------------------------------------------+
| Layer B: coordinate Fourier equivalence                       |
|                                                               |
|   How does the concrete transform act on P.placeCarrier V?     |
|   Is it identity, involution-backed, or a nontrivial operator? |
+-------------------------------+-------------------------------+
                                |
                                v
+---------------------------------------------------------------+
| Layer C: grade preservation                                   |
|                                                               |
|   If x is in a grade subspace, why is Fourier(x) still there?  |
|   This must be proved from B and the grade definition.         |
+-------------------------------+-------------------------------+
                                |
                                v
+---------------------------------------------------------------+
| Layer D: active CCM24 consumers                               |
|                                                               |
|   SourceSemilocalRows / SourceModelConstructorInput consume    |
|   the new owner, not identity/line compatibility wrappers.     |
+---------------------------------------------------------------+
```

The current line-span cut proves Layer C for the identity transform:

```text
fourierEquiv x = x
gradeSubspace v = span Real {v}
therefore x in gradeSubspace v -> fourierEquiv x in gradeSubspace v
```

That is Mathlib-bottom, but it does not yet encode a nontrivial CCM24 Fourier
transform.  The next cut must add a lower semantic owner for Layer A/B.


## 4. Hidden Assumptions To Challenge

Assumption 1:

```text
The next owner should replace SourceLineFourierCoordinateGradingData directly.
```

Challenge:

```text
Replacing it directly risks breaking active constructors before we know the
right transform semantics.  Safer sequence:

  add lower semantic owner
    -> derive SourceLineFourierCoordinateGradingData or a stronger coordinate
       Fourier owner from it
    -> rewire one active consumer
    -> only then deprecate the old active line owner.
```

Assumption 2:

```text
The concrete Fourier transform must be non-identity immediately.
```

Challenge:

```text
If the current concrete model intentionally identifies the Fourier transform
with identity after transport, then the real missing theorem is not
"non-identity"; it is a named theorem explaining why that identity is the
intended Fourier transform in this model.

The unacceptable part is not identity itself.  The unacceptable part is identity
as an unexplained endpoint.
```

Assumption 3:

```text
More Mathlib-bottom line-span lemmas equal deeper Fourier progress.
```

Challenge:

```text
No.  More line-span lemmas are prep-only unless a real consumer moves from the
old identity/line endpoint to a lower Fourier semantics owner.
```


## 5. Target Owner Shape

Preferred new owner name:

```text
SourceFourierTransformGradingSemanticsData
```

Owner module:

```text
ConnesWeilRH/Source/AnalyticCore.lean
```

Lean-ish field sketch:

```lean
structure SourceFourierTransformGradingSemanticsData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) where
  coordinateFourierEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    P.placeCarrier V ≃L[ℝ] P.placeCarrier V

  gradeIndex : Type

  coordinateGradeSubspace :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    gradeIndex -> Submodule ℝ (P.placeCarrier V)

  coordinateFourier_preserves_grade :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    forall n x,
      x ∈ coordinateGradeSubspace n ->
        coordinateFourierEquiv x ∈ coordinateGradeSubspace n

  transform_law :
    exact Lean type, pinned before this record is added, tying
    coordinateFourierEquiv to the concrete source Fourier/involution semantics
```

The first four fields are essentially the existing coordinate Fourier grading
surface.  The new information is `transform_law`.

Hard gate:

```text
Do not add this record until Batch 0 pins the exact Lean type of
transform_law and names the concrete declaration/theorem that proves it.

If Batch 0 cannot produce that type/proof source, stop with the strict blocker
report in Section 10.  Do not add a placeholder record with a bare Prop field.
```


## 6. Candidate Lower Laws

Candidate A: identity-backed law

```text
coordinateFourierEquiv = ContinuousLinearEquiv.refl Real (P.placeCarrier V)
```

Pros:

```text
Easy to prove.
Preserves current build behavior.
Can still be useful if the concrete source model intentionally realizes Fourier
as identity after place transport.
```

Cons:

```text
Does not deepen semantics unless paired with a named explanation:
  why is identity the concrete Fourier transform here?
```

Acceptance condition:

```text
Only acceptable if it deletes the active line-only owner path and records the
identity law as a theorem derived from concrete transform definitions, not as a
new arbitrary field.
```

Candidate B: involution-backed law

```text
coordinateFourierEquiv acts like the source-test involution transported to
P.placeCarrier V.
```

Pros:

```text
Connects to existing Fourier-support memory:
  S.fourierSupportCarrier S.sourceTest =
    S.supportCarrier (A.involution S.sourceTest)
```

Cons:

```text
May require support/window/involution semantics before the grading proof can
be nontrivial.
```

Acceptance condition:

```text
The proof must use existing involution/transform definitions, not a copied
field stating the result.

The support-carrier theorem
  S.fourierSupportCarrier f = S.supportCarrier (A.involution f)
is only candidate evidence.  It does not by itself define or justify a
coordinate operator:
  P.placeCarrier V ≃L[Real] P.placeCarrier V

Before Candidate B can be implemented, local type inspection must show the
transport theorem from source-test Fourier/involution semantics to the
placeCarrier continuous linear equivalence.
```

Candidate C: true Fourier-transform law on Mathlib Schwartz/TestFunction

```text
coordinateFourierEquiv is induced by the Mathlib Fourier transform on the
underlying test-function carrier.
```

Pros:

```text
Most semantically honest target.
```

Cons:

```text
Likely needs a broader TestFunction/Fourier API and may cross ownership into
route/arithmetic unless carefully scoped.
```

Acceptance condition:

```text
Only start this if local #check shows usable Mathlib/source declarations for
the concrete Fourier transform and its linear equivalence.
```

Recommended first cut:

```text
Start with Candidate B if existing involution laws are strong enough.
Fall back to Candidate A only if it is explicitly named as the current concrete
Fourier-realization theorem and deletes the old line-only consumer path.
Do not jump to Candidate C until local type inspection shows the exact Mathlib
Fourier API available in this project.
```


## 7. Implementation Batches

### Batch 0: Local Type Pinning

Purpose:

```text
Avoid speculative Lean edits.
```

Scratch checks:

```lean
import ConnesWeilRH.Source.AnalyticCore

#check ConnesWeilRH.Source.AnalyticCore.SourceSupportWindowData.SourceFourierGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceSupportWindowData.SourceFourierCoordinateGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceSupportWindowData.SourceLineFourierCoordinateGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierCoordinateGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierGradingData_fourierEquiv_apply
```

Search commands:

```text
rg -n "Fourier|fourier|involution|coordinateFourier|fourierEquiv" ConnesWeilRH/Source -g "*.lean"
rg -n "sourceFourierGradingModelData|ofLineFourierModelData|fixedWindowExhaustionCompatible_of_line" ConnesWeilRH -g "*.lean"
```

Exit condition:

```text
Exact owner declarations and current consumers are pinned before editing.
Exact transform_law Lean type is pinned.
Exact existing concrete proof source for transform_law is named.

If the proof source is absent, do not edit Lean code.  Produce the Section 10
blocker report instead.
```


### Batch 1: Add The Lower Semantic Owner

Goal:

```text
Introduce SourceFourierTransformGradingSemanticsData or a shorter project-style
name if existing naming suggests one.
```

Allowed file:

```text
ConnesWeilRH/Source/AnalyticCore.lean
```

Do:

```text
1. Add the record near SourceFourierCoordinateGradingData.
2. Add conversion:
     SourceFourierTransformGradingSemanticsData.toFourierCoordinateGradingData
3. Add conversion:
     SourceFourierTransformGradingSemanticsData.toFourierGradingData
4. Prove readback lemmas only if they expose real owner fields and are needed
   by the consumer migration.
```

Do not:

```text
Do not make transform_law a bare Prop with no concrete definition path.
Do not add this record before Batch 0 pins transform_law's exact Lean type and
proof source.
Do not add True / Set.univ / Unit-only semantic fields.
Do not count conversion wrappers as Mathlib-bottom.
```

Expected status:

```text
Project-bottom API boundary, not yet Mathlib-bottom, unless transform_law is
proved from existing concrete definitions.
```


### Batch 2: Concrete Provider

Goal:

```text
Add a concrete provider below concreteRealFourierGradingData.
```

Candidate names:

```text
concreteRealFourierTransformGradingSemanticsData
concreteRealFourierTransformGradingSemanticsData_toCoordinate
concreteRealFourierTransformGradingSemanticsData_fourierEquiv_apply
concreteRealFourierTransformGradingSemanticsData_preserves_grade
```

Preferred proof shape:

```text
If identity-backed:
  prove coordinateFourierEquiv_apply from ContinuousLinearEquiv.refl_apply
  prove preservation from hx

If involution-backed:
  prove coordinateFourierEquiv_apply from the concrete involution/Fourier law
  prove preservation using the grade-subspace definition and the transform law
```

Minimum useful Mathlib-bottom bricks:

```text
concrete provider's fourierEquiv apply theorem
concrete provider's inverse/apply theorem, if exposed
concrete provider's gradeSubspace membership theorem
concrete provider's Fourier-preserves-grade theorem
```

These count only if focused `#print axioms` has no project-local axiom,
`sorryAx`, hidden Prop field, endpoint package, or certificate atom.


### Batch 3: Rewire SourceSemilocalRows

Goal:

```text
Move active SourceSemilocalRows Fourier input from line-only data to the new
semantic owner.
```

Old active path to lower:

```text
SourceSemilocalRows.sourceFourierGradingModelData :
  forall V H,
    SourceLineFourierCoordinateGradingData S (P := sourcePlaceCarrierData) V
```

New active path:

```text
SourceSemilocalRows.sourceFourierTransformGradingSemanticsData :
  forall V H,
    SourceFourierTransformGradingSemanticsData S H
```

Compatibility bridge:

```text
If old line-grading accessors are still needed, derive them from the new owner
or keep a compatibility constructor.  Do not let the old line owner remain the
active SourceSemilocalRows field.
```

Consumer rewires:

```text
SourceSemilocalRows.sourceFourierGradingData
SourceSemilocalRows.ofLineFourierModelData or replacement constructor
SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows
```

Acceptance condition:

```text
rg shows no active constructor requirement for
SourceLineFourierCoordinateGradingData in SourceSemilocalRows.
```


### Batch 4: Rewire SourceModelConstructorInput

Goal:

```text
Move active CCM24 source-model constructor input to the new semantics owner.
```

Old active path:

```text
SourceModelConstructorInput.sourceFourierGradingModelData :
  forall V H,
    SourceLineFourierCoordinateGradingData ...
```

New active path:

```text
SourceModelConstructorInput.sourceFourierTransformGradingSemanticsData :
  forall V H,
    SourceFourierTransformGradingSemanticsData ...
```

Consumer rewires:

```text
SourceModelConstructorInput.sourceFourierGradingData
SourceModelConstructorInput.sourceFixedWindowCompatible
SourceModelConstructorInput.toSourceSemilocalRows
normalizedCoreSourceModelConstructorInputFromTheorems
concreteSemilocalRows
concreteFixedWindowExhaustionCompatible
```

Acceptance condition:

```text
The theorem-base / normalized constructor path uses the concrete semantic
provider directly.
```


### Batch 5: Remove Or Demote Old Active Line Path

Goal:

```text
Make SourceLineFourierCoordinateGradingData a compatibility surface only.
```

Keep:

```text
Line-span Mathlib-bottom lemmas may stay as reusable support lemmas.
```

Remove from active path:

```text
SourceSemilocalRows.sourceFourierGradingModelData as line-only input
SourceModelConstructorInput.sourceFourierGradingModelData as line-only input
fixedWindowExhaustionCompatible_of_line_fourier_coordinate_model_data as the
active fixed-window Fourier path
```

Possible replacement:

```text
fixedWindowExhaustionCompatible_of_fourier_transform_grading_semantics_data
```

Acceptance condition:

```text
rg -n "ofLineFourierModelData|fixedWindowExhaustionCompatible_of_line|SourceLineFourierCoordinateGradingData" \
  ConnesWeilRH/Source -g "*.lean"

Expected:
  hits are compatibility definitions/theorems only, not active constructor
  fields or theorem-base provider paths.
```


## 8. Verification Plan

Small local checks:

```text
lake env lean ConnesWeilRH/Source/AnalyticCore.lean
lake env lean ConnesWeilRH/Source/AnalyticSourceModel.lean
```

Smallest owning builds:

```text
lake build ConnesWeilRH.Source.AnalyticSourceModel ConnesWeilRH.Source.CCM24SourceModel
```

If route-facing consumers change:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Required WSL discipline:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.AnalyticSourceModel ConnesWeilRH.Source.CCM24SourceModel'
```

Focused axiom audit:

```text
For every claimed Mathlib-bottom theorem:
  #check theorem_name
  #print theorem_name
  #print axioms theorem_name
```

Good audit:

```text
[propext, Classical.choice, Quot.sound]
```

Bad audit:

```text
sorryAx
project-local axiom
constant / opaque / unsafe dependency
free project-local Prop field
endpoint package theorem
certificate atom
```


## 9. Rejection Rules

Reject the batch if it only:

```text
renames SourceLineFourierCoordinateGradingData
adds a readback theorem around concreteRealFourierGradingData
adds another compatibility constructor
proves identity preservation without tying identity to a named transform law
uses Unit as the new semantic owner
adds True / Set.univ
leaves active consumers on the old line-only field
```


## 10. Expected First Real Blocker

Likely first blocker:

```text
The project may not yet have a nontrivial concrete Fourier transform on
P.placeCarrier V that is strong enough to define a ContinuousLinearEquiv and
prove grade preservation.
```

If that happens, the correct blocked report is:

```text
first non-Mathlib black box:
  exact missing concrete Fourier transform/equivalence declaration

exact declaration/type:
  Lean-ish type of the missing transform law

why the current proof path stops there:
  current source can only prove identity/line-span preservation

concrete lower definition or Mathlib theorem needed next:
  the concrete Fourier/involution equivalence on P.placeCarrier V
  or theorem that the current identity realization is definitionally the
  intended Fourier transform

files/declarations inspected:
  ConnesWeilRH/Source/AnalyticCore.lean
  ConnesWeilRH/Source/AnalyticSourceModel.lean
  ConnesWeilRH/Source/CCM24SourceModel.lean

evidence:
  rg and #check output naming the absent or insufficient declaration
```


## 11. Recommended Execution Order

```text
1. Pin local types and current active consumers.
2. Search for existing concrete Fourier/involution law.
3. If a real law exists:
     add SourceFourierTransformGradingSemanticsData with that law.
   Else:
     stop and write the strict blocker report.  Do not add a new API-boundary
     sketch unless it deletes an old active path without introducing a bare
     project-local Prop.
4. Add concrete provider.
5. Rewire SourceSemilocalRows.
6. Rewire SourceModelConstructorInput.
7. Demote old line-only path to compatibility.
8. Run smallest WSL build.
9. Run focused axiom audit.
10. Record accepted result in MEMORY.md only after build and audit pass.
```


## 12. Bottom Line

The next Fourier cut should not try to prove more facts about:

```text
span Real {v}
identity Fourier equivalence
line grading readbacks
```

unless those facts are used to move an active consumer to a lower transform
semantics owner.

The target is:

```text
line-span grading as a compatibility implementation detail
    ↓
named Fourier transform / grading semantics owner
    ↓
concrete provider tied to transform or involution semantics
    ↓
SourceSemilocalRows and SourceModelConstructorInput consume the new owner
```
