# A4 CCM24 Fourier Carrier-Transport Completion Plan

Date: 2026-07-06

Status: planning artifact only.  This file defines the missing completion step
for the CCM24 Fourier transform / grading lane.  It is not accepted Lean
progress and does not claim an unconditional proof of `_root_.RiemannHypothesis`.


## 1. Result First

The current Fourier lane still fails the hard semantic gate because the new
transform owner proves:

```text
concreteRealCoordinateFourierEquiv =
  intendedConcreteRealCoordinateFourierEquiv
```

but the current intended object is only:

```text
intendedConcreteRealCoordinateFourierEquiv :=
  concreteRealCoordinateFourierEquiv
```

That is a same-object alias, not a carrier-transport theorem.

The missing proof is:

```text
coordinate Fourier equivalence on the concrete place carrier
  =
the source Fourier/involution action transported through the concrete
place-realization map.
```


## 2. Current Evidence

Current concrete source Fourier/involution fact:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean

concreteTestAlgebra.involution f = FourierTransform.fourier f
```

This is good: source-level involution is definitionally Fourier.

Current carrier-level operator:

```text
ConnesWeilRH/Source/AnalyticCore.lean

concreteRealCoordinateFourierEquiv I sourceTest V =
  ContinuousLinearEquiv.refl Real (P.placeCarrier V)
```

Current problematic intended operator:

```text
intendedConcreteRealCoordinateFourierEquiv I sourceTest V :=
  concreteRealCoordinateFourierEquiv I sourceTest V
```

Current active provider:

```text
concreteRealFourierCoordinateGradingData
  -> concreteRealCoordinateFourierTransformSemanticsData
  -> toFourierCoordinateGradingData
```

This active provider no longer directly uses:

```text
concreteRealLineFourierCoordinateGradingData.toIdentity...
```

But the transform law still collapses to an alias.


## 3. Completion Definition

A4 is solved only when there is a named theorem of this form:

```text
concreteRealCoordinateFourierEquiv
  =
transported source Fourier/involution action on P.placeCarrier V
```

The theorem must not prove equality against an alias that was defined to be
`concreteRealCoordinateFourierEquiv`.

Acceptable completion theorem names:

```text
concreteRealCoordinateFourierEquiv_eq_transported_source_fourier
concreteRealCoordinateFourierEquiv_eq_transported_source_involution
concreteRealFourierCoordinateGradingData_transport_law
```

Rejected theorem names/shapes:

```text
concreteRealCoordinateFourierEquiv_realizes_source_involution
  if it is only rfl against intendedConcreteRealCoordinateFourierEquiv

intendedConcreteRealCoordinateFourierEquiv_source_involution
  if it only proves source-level involution = Fourier without touching the
  coordinate carrier action
```


## 4. First-Principles Shape

The real semantic chain is:

```text
+-------------------------------------------------------------+
| Source test layer                                           |
|                                                             |
|   concreteTestAlgebra.involution f = FourierTransform.fourier f |
+-----------------------------+-------------------------------+
                              |
                              v
+-------------------------------------------------------------+
| Source-to-carrier realization                               |
|                                                             |
|   how a source-test transform induces an operator on         |
|   P.placeCarrier V                                          |
+-----------------------------+-------------------------------+
                              |
                              v
+-------------------------------------------------------------+
| Concrete coordinate carrier                                 |
|                                                             |
|   concreteRealCoordinateFourierEquiv                         |
+-----------------------------+-------------------------------+
                              |
                              v
+-------------------------------------------------------------+
| Fourier grading provider                                    |
|                                                             |
|   concreteRealFourierCoordinateGradingData                   |
+-------------------------------------------------------------+
```

The missing box is the middle one:

```text
source-to-carrier realization
```

Without it, source Fourier and coordinate Fourier are two separate facts.


## 5. Required Static Inspection

Before editing, inspect these exact declarations:

```text
rg -n "ConcreteRealCoordinateFourierTransformSemanticsData|intendedConcreteRealCoordinateFourierEquiv|concreteRealCoordinateFourierEquiv|concreteTestAlgebra_involution" ConnesWeilRH/Source -g "*.lean"

rg -n "placeEquiv|placeCarrier|legacy|encode|decode|FourierTransform.fourier|involution" ConnesWeilRH/Source/AnalyticCore*.lean
```

Pin the types:

```lean
import ConnesWeilRH.Source.AnalyticCore

#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealCoordinateFourierEquiv
#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.intendedConcreteRealCoordinateFourierEquiv
#check ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra_involution
#check ConnesWeilRH.Source.AnalyticCore.SourceSupportWindowData.SourceCanonicalHilbertModelData.placeEquiv
```


## 6. Implementation Route

### Step A4.1: Replace Alias With Transported Operator

Add a definition whose name makes the semantic transport explicit:

```lean
noncomputable def transportedConcreteSourceFourierCoordinateEquiv
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealPlaceCarrierData I sourceTest).placeCarrier V ≃L[ℝ]
      (concreteRealPlaceCarrierData I sourceTest).placeCarrier V := ...
```

Important:

```text
Do not define this by simply returning concreteRealCoordinateFourierEquiv.
```

It must be defined from the source-to-carrier realization available in this
project.  If the concrete place carrier is currently `Real` with no dependence
on source tests, the definition may be `ContinuousLinearEquiv.refl`, but the
name and theorem must state why the transported source Fourier action is
identity on this carrier.

Acceptable if current model has no nontrivial carrier action:

```lean
noncomputable def transportedConcreteSourceFourierCoordinateEquiv ... :=
  ContinuousLinearEquiv.refl ℝ ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V)
```

but only if accompanied by a theorem:

```lean
theorem transportedConcreteSourceFourierCoordinateEquiv_eq_refl_of_source_fourier
    (...) :
    transportedConcreteSourceFourierCoordinateEquiv I sourceTest V =
      ContinuousLinearEquiv.refl ℝ
        ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V) := ...
```

and the proof explanation must cite:

```text
Concrete placeCarrier V is Real and currently records no nontrivial action of
the source test Fourier transform.  Therefore the transported action in the
current concrete carrier model is identity.
```

This is still a model limitation, but it is an explicit limitation rather than
an alias.


### Step A4.2: Redefine Intended Operator

Change:

```lean
intendedConcreteRealCoordinateFourierEquiv :=
  concreteRealCoordinateFourierEquiv
```

to:

```lean
intendedConcreteRealCoordinateFourierEquiv :=
  transportedConcreteSourceFourierCoordinateEquiv
```

This is the key cut.  The intended operator must be the transported source
Fourier/involution action, not the already-existing coordinate operator.


### Step A4.3: Prove The Carrier-Transport Equality

Add:

```lean
theorem concreteRealCoordinateFourierEquiv_eq_transported_source_fourier
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    concreteRealCoordinateFourierEquiv I sourceTest V =
      transportedConcreteSourceFourierCoordinateEquiv I sourceTest V := by
  ...
```

Then rewrite the existing theorem:

```lean
theorem concreteRealCoordinateFourierEquiv_realizes_source_involution ...
```

so it uses the new theorem, not `rfl` against a same-object alias.


### Step A4.4: Strengthen Transform Semantics Data

Ensure:

```lean
ConcreteRealCoordinateFourierTransformSemanticsData.coordinateFourier_transform_law
```

now points to:

```text
concreteRealCoordinateFourierEquiv_eq_transported_source_fourier
```

and not to a definitional alias.

Keep:

```lean
source_involution_transform_law :
  forall f, concreteTestAlgebra.involution f = FourierTransform.fourier f
```

but treat it as source-layer evidence only.  It is not enough by itself.


### Step A4.5: Reaudit Consumers

Required active path:

```text
normalizedCoreSourceModelConstructorInputFromTheorems
  -> concreteRealFourierCoordinateGradingData
  -> concreteRealCoordinateFourierTransformSemanticsData
  -> transportedConcreteSourceFourierCoordinateEquiv
```

Search:

```text
rg -n "intendedConcreteRealCoordinateFourierEquiv :=\\s*concreteRealCoordinateFourierEquiv|concreteRealCoordinateFourierEquiv_realizes_source_involution.*rfl|concreteRealFourierCoordinateGradingData" ConnesWeilRH/Source -g "*.lean"
```

Rejected if:

```text
intendedConcreteRealCoordinateFourierEquiv still aliases
concreteRealCoordinateFourierEquiv.
```


## 7. Verification

Smallest source build:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.AnalyticSourceModel ConnesWeilRH.Source.CCM24SourceModel'
```

Focused axiom audit:

```lean
import ConnesWeilRH.Source.AnalyticSourceModel
import ConnesWeilRH.Source.CCM24SourceModel

#print axioms ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.transportedConcreteSourceFourierCoordinateEquiv_eq_refl_of_source_fourier
#print axioms ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealCoordinateFourierEquiv_eq_transported_source_fourier
#print axioms ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealCoordinateFourierEquiv_realizes_source_involution
#print axioms ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierCoordinateGradingData_transform_law
#print axioms ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierCoordinateGradingData_source_involution
#print axioms ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierGradingData_fourierEquiv_apply
#print axioms ConnesWeilRH.Source.AnalyticCore.SourceModelConstructorInput.sourceFourierGradingData
```

Acceptable output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local axiom
constant / opaque / unsafe
free Prop field stating transport
```


## 8. Acceptance Statement

Use this exact final wording if the gate passes:

```text
Result:
  Good.  A4 closes the CCM24 concrete Fourier carrier-transport gap for the
  current concrete model.  This is not an unconditional RH proof.

Old weak path removed:
  intendedConcreteRealCoordinateFourierEquiv no longer aliases
  concreteRealCoordinateFourierEquiv.

New lower theorem:
  concreteRealCoordinateFourierEquiv_eq_transported_source_fourier

Semantic preservation:
  The theorem proves the concrete coordinate Fourier equivalence is the
  transported source Fourier/involution action on the current concrete place
  carrier.  Since the current concrete place carrier is Real with no nontrivial
  source-test action, the transported action is identity, but this is now an
  explicit model theorem rather than a same-object alias.

Remaining boundary:
  If later CCM24 requires a nontrivial spectral/Fourier decomposition, the next
  boundary is enriching the concrete place carrier model itself, not the current
  Fourier grading compatibility path.
```


## 9. Bottom Line

A4 is not about adding more line-span facts.

A4 is about replacing:

```text
intended Fourier = current coordinate Fourier
```

with:

```text
current coordinate Fourier =
transported source Fourier/involution action
```

Only that closes the hard-gate gap identified in the last verification.
