/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalResidual
import ConnesWeilRH.Dev.C1Stage3ProjectionKernel

/-!
# C1 selected-detector semi-local residual decomposition

The visible Euler residual is now a genuine same-owner operator.  To identify
what a finite-part construction must control, this module re-proves from active
CCM24 source definitions the projection identity

```text
R_0 - R_S = (K_S - K_0) - E (Q_S - Q_0) E.
```

Here `K_0` and `K_S` are the archimedean and semi-local prolate remainders,
and `E (Q_S - Q_0) E` is the finite-place Fourier-compression change.  After
the selected detector and literal Euler boundary are inserted, the Euler
residual becomes exactly

```text
(detector (K_S - K_0) - visible Euler boundary)
  - detector (E (Q_S - Q_0) E).
```

This is an exact geometric decomposition, not a vanishing, a finite-part, or
a positivity claim.  It makes clear that a viable semi-local finite-part must
account for both named terms on the same carrier.  The old frozen Gate-3U
ledger is not imported.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SelectedDetectorSemiLocalResidualDecomposition

open CC20Concrete
open CCM25Concrete
open CCM25Concrete.SelectedWeilSquare
open C1SelectedDetectorSemiLocalEulerBoundary
open C1SelectedDetectorSemiLocalResidual
open C1Stage3ProjectionKernel
open C1Stage3ProjectionTraceLedger

noncomputable section

/-- The archimedean prolate remainder `K_0 = E Q_0 E - R_0` on the common
semi-local carrier. -/
noncomputable def archimedeanProlateKernel (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection ∘L
      radialSupportProjection lambda -
    sourceSoninProjection lambda

/-- The difference between the semi-local and archimedean Fourier
compressions, both restricted by the same radial projection. -/
noncomputable def semiLocalFourierCompressionDifference
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L
      (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule.starProjection ∘L
      radialSupportProjection lambda -
    radialSupportProjection lambda ∘L
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection ∘L
      radialSupportProjection lambda

/-- The prolate change `K_S - K_0` between the semi-local positive core and
the archimedean prolate remainder. -/
noncomputable def semiLocalProlateDifference
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  stage3ProjectionKernel lambda S - archimedeanProlateKernel lambda

/-- Exact projection geometry: the active Sonin-band difference equals the
prolate change minus the Fourier-compression change. -/
theorem soninBandDifference_eq_semiLocalProlate_sub_compression
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    soninBandDifference lambda S =
      semiLocalProlateDifference lambda S -
        semiLocalFourierCompressionDifference lambda S := by
  simp only [soninBandDifference, semiLocalProlateDifference,
    semiLocalFourierCompressionDifference, stage3ProjectionKernel,
    archimedeanProlateKernel, radialSupportProjection,
    targetSoninProjection, sourceSoninProjection]
  abel

/-- The selected response is a detector-weighted prolate change, less its
detector-weighted semi-local Fourier-compression change. -/
theorem projectionResponse_eq_semiLocalProlate_sub_compression
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) :
    projectionResponse owner lambda S =
      detectorOperator owner ∘L semiLocalProlateDifference lambda S -
        detectorOperator owner ∘L
          semiLocalFourierCompressionDifference lambda S := by
  rw [projectionResponse, soninBandDifference_eq_semiLocalProlate_sub_compression]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub]

/-- The first named piece of the visible Euler residual: the detector-weighted
prolate change with the literal Euler boundary removed. -/
noncomputable def selectedEulerProlateResidual
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) (data : VisiblePrimePowerTerms S) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  detectorOperator owner ∘L semiLocalProlateDifference lambda S -
    selectedEulerLogBoundaryPairOperatorSum owner data

/-- The actual visible Euler residual has exactly two geometric channels.
Neither channel is asserted to have a sign or a small trace. -/
theorem selectedEulerBoundaryResidual_eq_prolate_sub_compression
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) (data : VisiblePrimePowerTerms S) :
    selectedEulerBoundaryResidual owner lambda S data =
      selectedEulerProlateResidual owner lambda S data -
        detectorOperator owner ∘L
          semiLocalFourierCompressionDifference lambda S := by
  rw [selectedEulerBoundaryResidual,
    projectionResponse_eq_semiLocalProlate_sub_compression,
    selectedEulerProlateResidual]
  abel

end
end C1SelectedDetectorSemiLocalResidualDecomposition
end Source
end ConnesWeilRH
