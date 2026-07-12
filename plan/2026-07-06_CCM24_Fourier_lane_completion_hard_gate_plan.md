# CCM24 Fourier Lane Completion Hard-Gate Plan

Date: 2026-07-06

Status: planning artifact only.  This document defines the hard gate for
claiming the CCM24 Fourier transform / grading lane is solved.  It is not Lean
proof progress and does not claim an unconditional proof of
`_root_.RiemannHypothesis`.


## 1. Result First

The current lane is not solved if the active concrete provider still follows
this shape:

```text
concreteRealFourierCoordinateGradingData
  -> concreteRealLineFourierCoordinateGradingData
  -> toIdentityFourierCoordinateGradingData
  -> toFourierCoordinateGradingData
```

That path may be build-clean and axiom-clean, but it is still semantically too
weak unless there is a separate Lean theorem proving that this identity/line
realization is the intended CCM24 Fourier transform in the concrete model.

The completion target is:

```text
active CCM24 Fourier consumers
  -> concrete Fourier-coordinate grading owner
  -> named transform semantics owner
  -> proof that the transform preserves the grading
  -> proof that this transform is the intended CCM24 Fourier/involution object
```


## 2. What Counts As Solved

Exactly one of these two routes must be completed.

### Route A: Real Transform / Involution Owner

Solved if:

```text
1. A named source-local lower owner exists for concrete Fourier/involution
   semantics.

2. concreteRealFourierCoordinateGradingData is constructed from that owner,
   not from SourceLineFourierCoordinateGradingData.toIdentity...

3. The owner proves:
     coordinateFourierEquiv_apply
     coordinateFourierEquiv_symm_apply or inverse law
     coordinateFourier_preserves_grade
     transform law tying coordinateFourierEquiv to source Fourier/involution

4. SourceSemilocalRows and SourceModelConstructorInput consume the resulting
   SourceFourierCoordinateGradingData path.

5. The old line/identity provider remains only as compatibility or support
   lemma, not as the active concrete Fourier semantics endpoint.
```

### Route B: Identity-Is-The-Real-Fourier Theorem

Solved if:

```text
1. The concrete model intentionally realizes the CCM24 Fourier transform as
   identity after place transport.

2. Lean contains a named theorem proving that fact from concrete source
   definitions, not by adding a bare Prop field.

3. concreteRealFourierCoordinateGradingData may still use identity, but the
   active semantics endpoint is the identity-is-real theorem, not the line
   provider itself.

4. The theorem is used by the active consumer path or by the concrete provider
   constructor.
```

Acceptable theorem shape:

```lean
theorem concreteRealFourierTransform_realized_by_identity
    (...) :
    concreteRealFourierTransformEquiv I sourceTest V H =
      ContinuousLinearEquiv.refl ℝ H.hilbertCarrier := ...
```

or, if the project works at coordinate carrier level:

```lean
theorem concreteRealCoordinateFourierEquiv_realizes_source_involution
    (...) :
    concreteRealCoordinateFourierEquiv I sourceTest V =
      intendedCoordinateFourierEquiv I sourceTest V := ...
```

The exact names may differ, but the statement must connect the identity-like
operator to the intended Fourier/involution semantics.


## 3. What Does Not Count

Reject the lane-completion claim if any of these remain true:

```text
concreteRealFourierCoordinateGradingData is still definitionally built from
  concreteRealLineFourierCoordinateGradingData.toIdentity...

SourceFourierCoordinateGradingData is only used as a larger wrapper around the
  same line/identity implementation.

The only new theorems prove:
  fourierEquiv x = x
  x in span Real {v}
  line-span membership
  compatibility constructor readbacks
  projection facts from SourceFourierCoordinateGradingData

No theorem identifies the Fourier equivalence with the intended CCM24
  Fourier/involution transform.

The active route consumer still has no stronger statement than
  S.fourierGradingCompatible V.
```

Short version:

```text
Coordinate-owner migration is not completion.
Identity/line-span proof is not completion.
Axiom-clean wrapper theorem is not completion.
```


## 4. Current Known State To Start From

The latest implementation appears to have completed this intermediate step:

```text
SourceSemilocalRows.sourceFourierGradingModelData :
  forall V H, SourceFourierCoordinateGradingData S H

SourceModelConstructorInput.sourceFourierGradingModelData :
  forall V H, SourceFourierCoordinateGradingData core.supportWindow H

SourceSupportWindowData.fixedWindowExhaustionCompatible_of_fourier_coordinate_model_data
  is the active fixed-window constructor path.
```

This is useful because it removes the line-only type from the active field.

But the concrete provider still needs to be checked against this red line:

```text
concreteRealFourierCoordinateGradingData
  must not remain a line/identity-derived endpoint
  unless Route B is proved.
```


## 5. First-Principles Model

Fourier grading has three independent semantic obligations:

```text
+---------------------------------------------------------------+
| 1. Operator meaning                                            |
|                                                               |
|    What is the Fourier transform/involution on the current     |
|    source carrier?                                            |
+-------------------------------+-------------------------------+
                                |
                                v
+---------------------------------------------------------------+
| 2. Carrier transport                                           |
|                                                               |
|    How is that operator transported through placeEquiv into    |
|    H.hilbertCarrier or P.placeCarrier V?                       |
+-------------------------------+-------------------------------+
                                |
                                v
+---------------------------------------------------------------+
| 3. Grading preservation                                        |
|                                                               |
|    Why does the transported operator preserve the selected     |
|    grade subspaces?                                           |
+---------------------------------------------------------------+
```

The previous line-span work solved only a special case of obligation 3:

```text
operator = identity
gradeSubspace v = span Real {v}
therefore preservation is immediate
```

The missing part is obligation 1:

```text
why is this the Fourier transform required by CCM24?
```


## 6. Required Static Inspection Before Editing

Run these searches and record the exact results before touching code:

```text
rg -n "concreteRealFourierCoordinateGradingData|concreteRealFourierGradingData|coordinateFourierEquiv|fourierEquiv_apply" ConnesWeilRH/Source -g "*.lean"

rg -n "involution|FourierTransform|fourierTransform|sourceFourierSupportCarrier_eq_involutionSupport|coordinateFourier" ConnesWeilRH/Source -g "*.lean"

rg -n "sourceFourierGradingModelData|ofFourierCoordinateModelData|ofLineFourierModelData|fixedWindowExhaustionCompatible_of_fourier_coordinate|fixedWindowExhaustionCompatible_of_line" ConnesWeilRH -g "*.lean"
```

Then pin local types:

```lean
import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.AnalyticSourceModel

#check ConnesWeilRH.Source.AnalyticCore.SourceSupportWindowData.SourceFourierCoordinateGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceSupportWindowData.SourceFourierGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierCoordinateGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierGradingData
#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierGradingData_fourierEquiv_apply
```

If no source-local concrete Fourier/involution law exists, do not fake one.
Write the missing declaration type first.


## 7. Implementation Plan

### Batch 1: Name The Missing Transform Semantics

Preferred owner family:

```text
SourceFourierTransformSemanticsData
SourceCoordinateFourierTransformSemanticsData
ConcreteRealFourierTransformSemanticsData
```

Choose the narrowest name that matches the existing namespace style.

Target location:

```text
ConnesWeilRH/Source/AnalyticCore.lean
```

Minimal acceptable owner shape:

```lean
structure SourceCoordinateFourierTransformSemanticsData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} (V : S.PlaceSet) where
  coordinateFourierEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    P.placeCarrier V ≃L[ℝ] P.placeCarrier V

  coordinateFourier_transform_law :
    -- Must mention the intended concrete Fourier/involution object.
    -- Do not leave this as an arbitrary free Prop.
    ...
```

If the exact transform law cannot yet be written, stop here and report:

```text
first non-Mathlib black box:
  missing source-local Fourier/involution transform law

exact declaration/type:
  <Lean-ish type discovered from local #check / rg>
```

Do not proceed with another identity wrapper.


### Batch 2: Derive Coordinate Grading From Transform Semantics

Add a constructor:

```lean
noncomputable def SourceCoordinateFourierTransformSemanticsData.toFourierCoordinateGradingData
    (...) :
    SourceFourierCoordinateGradingData S H := ...
```

This constructor must use:

```text
coordinateFourierEquiv from the transform semantics owner
coordinateFourier_preserves_grade proved from the transform law and grade model
```

It must not use:

```text
SourceLineFourierCoordinateGradingData.toIdentityFourierCoordinateGradingData
as its source of Fourier semantics.
```


### Batch 3: Concrete Provider Replacement

Replace the active concrete provider:

```text
old:
  concreteRealFourierCoordinateGradingData
    := line.toIdentity.toFourierCoordinateGradingData

new:
  concreteRealFourierCoordinateGradingData
    := concreteRealFourierTransformSemanticsData.toFourierCoordinateGradingData
```

Required concrete theorem names:

```text
concreteRealCoordinateFourierTransformSemanticsData
concreteRealCoordinateFourierEquiv_apply
concreteRealCoordinateFourierEquiv_symm_apply
concreteRealCoordinateFourier_preserves_grade
concreteRealFourierCoordinateGradingData_transform_law
```

Names may be adjusted for project style, but the theorem set must cover:

```text
operator apply
inverse/symmetry
preservation of grade
connection to intended transform/involution
```


### Batch 4: Consumer Rewire Check

The latest migration may already have this part mostly done.  Verify and keep:

```text
SourceSemilocalRows.sourceFourierGradingModelData :
  forall V H, SourceFourierCoordinateGradingData S H

SourceModelConstructorInput.sourceFourierGradingModelData :
  forall V H, SourceFourierCoordinateGradingData core.supportWindow H

SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows :
  consumes SourceFourierCoordinateGradingData
```

Then ensure concrete/theorem-base producers use the new concrete transform
semantics provider, not the line provider.

Required scans:

```text
rg -n "concreteRealLineFourierCoordinateGradingData.*toIdentity|toIdentityFourierCoordinateGradingData.*toFourierCoordinateGradingData" ConnesWeilRH/Source -g "*.lean"

rg -n "ofLineFourierModelData|fixedWindowExhaustionCompatible_of_line_fourier_coordinate_model_data" ConnesWeilRH -g "*.lean"
```

Allowed remaining hits:

```text
compatibility constructors
old theorem wrappers explicitly marked compatibility
line-span support lemmas
```

Rejected remaining hits:

```text
concreteRealFourierCoordinateGradingData definition
concreteSemilocalRows
concreteFixedWindowExhaustionCompatible
normalizedCoreSourceModelConstructorInputFromTheorems
SourceModelConstructorInput.toSourceSemilocalRows
SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows
```


### Batch 5: Route-Sufficiency Check

Do not stop at source-local compatibility.

Answer this question in Lean terms:

```text
What downstream route/source theorem uses S.fourierGradingCompatible V, and is
the new statement strong enough for the next RH route step?
```

Required search:

```text
rg -n "fourierGradingCompatible|sourceFourierGradingData|FourierGrading" ConnesWeilRH/Route ConnesWeilRH/Source ConnesWeilRH/Dev -g "*.lean"
```

If all downstream consumers still erase the new semantics into:

```text
S.fourierGradingCompatible V
```

then record this as:

```text
Fourier transform semantics owner is built, but route still has a semantic
erasure boundary.  Next lower/upper route consumer must be strengthened.
```

Do not call the full lane solved unless either:

```text
the route only needs the compatibility predicate and the new owner proves that
predicate from real transform semantics;
```

or:

```text
the route consumer has been upgraded to read the stronger transform semantics
directly.
```


## 8. Verification Gates

### Build Gate

Always sync first:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'
```

Smallest owning build:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.AnalyticSourceModel ConnesWeilRH.Source.CCM24SourceModel'
```

If route-facing declarations change:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Route.RouteTheorem'
```

### Axiom Gate

For every claimed theorem:

```lean
#check theorem_name
#print theorem_name
#print axioms theorem_name
```

Acceptable:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected:

```text
sorryAx
project-local axiom
constant
opaque
unsafe
free Prop field that states the transform law
endpoint/package/certificate atom
```

### Semantic Gate

Before saying solved, run:

```text
rg -n "concreteRealFourierCoordinateGradingData|toIdentityFourierCoordinateGradingData|concreteRealLineFourierCoordinateGradingData|fourierEquiv_apply" ConnesWeilRH/Source/AnalyticCore.lean
```

Then answer:

```text
Does concreteRealFourierCoordinateGradingData still get its Fourier operator
from identity/line data?

If yes:
  Where is the Lean theorem proving identity is the intended CCM24 Fourier
  transform?

If no:
  What lower transform/involution owner supplies the operator?
```

No answer means no completion.


## 9. Handoff Template For Final Acceptance

Use this exact shape:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  concreteRealFourierCoordinateGradingData no longer derives from ...

New semantic owner:
  <exact declaration>

Transform law:
  <exact theorem>

Consumer rewires:
  SourceSemilocalRows...
  SourceModelConstructorInput...
  CCM24 package/source producer...

Semantic sufficiency:
  Explain why the new statement is strong enough for the next route/RH step,
  or name the next route erasure boundary.

Smallest WSL build:
  <command>

Build result:
  passed / failed

Focused axiom audit:
  <theorem list and exact axiom output>

First remaining non-Mathlib black box:
  <exact declaration/type, or "none in this lane" only if justified>
```


## 10. Bottom Line

The next implementation must not stop at:

```text
line owner -> coordinate owner
```

It must complete one of:

```text
real Fourier/involution semantics owner
```

or:

```text
identity-is-the-real-Fourier theorem
```

Without one of those, this lane is not solved.
