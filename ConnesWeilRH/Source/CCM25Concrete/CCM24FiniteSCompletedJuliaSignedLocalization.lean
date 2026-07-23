/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaSynthesis

/-!
# Local signed localization in the completed Julia cascade

The local raw defect has three different geometric contributions.  This
module separates them before any trace or norm is taken:

```text
local raw
  = local first jet
    + local polar Julia contribution
    + local route/polar ordering residual.
```

The polar contribution is the negative local relative numerator.  With this
sign it factors through the actual left Julia co-defect of the adjacent polar
frames.  The remaining first-jet-plus-ordering term is retained as an exact
non-polar localization gap.  A final equivalence identifies factorization of
that gap as precisely the missing producer for factorization of the full raw
defect through the same Julia slot.

The suffix-scaled version is connected to the existing corrected signed
cocycle: its local ordering residual is the one-step increment of the global
route/polar ordering defect.  No factorization of the non-polar gap, uniform
estimate, Gate 3U theorem, sign statement, or RH premise is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaSignedLocalization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSBandTrace
open CCM24FiniteSCompletedJuliaSynthesis
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovCompletedReadout
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Unscaled local signed decomposition -/

/-- The one-prime first-jet increment before the scalar of the remaining
suffix is inserted. -/
noncomputable def suffixActualBandLocalFirstJetContribution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (primeSchurMarkovScalar p : ℂ) •
      suffixActualBandFirstJetCycledResponse owner lambda (p :: S) -
    suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandFirstJetCycledResponse owner lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S

/-- The route-ordered endpoint increment before the scalar of the remaining
suffix is inserted. -/
noncomputable def suffixActualBandLocalRouteEndpointDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (primeSchurMarkovScalar p : ℂ) •
      suffixActualBandEndpointCycledResponse owner lambda (p :: S) -
    suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandEndpointCycledResponse owner lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S

/-- The sign of the local polar term as it occurs in the raw completed
response.  The relative numerator itself is subtracted in the corrected
cocycle, so the Julia-localized contribution is its negative. -/
noncomputable def suffixActualBandLocalPolarJuliaContribution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  -suffixEulerDetectorRelativeNumerator owner lambda p S

/-- The exact difference between polar ordering and route ordering.  This
orientation is the one used by the global corrected signed cocycle. -/
noncomputable def suffixActualBandLocalRoutePolarOrderingResidual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixEulerDetectorRelativeNumerator owner lambda p S -
    suffixActualBandLocalRouteEndpointDefect owner lambda p S

/-- The literal local raw defect is the signed sum of the first jet, the
Julia-localized polar term, and the route/polar ordering residual. -/
theorem suffixActualBandLocalRawDefect_eq_signedLocalization
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRawDefect owner lambda p S =
      suffixActualBandLocalFirstJetContribution owner lambda p S +
        suffixActualBandLocalPolarJuliaContribution owner lambda p S +
          suffixActualBandLocalRoutePolarOrderingResidual owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandLocalRawDefect,
    suffixActualBandRawQuadraticCycledResponse,
    suffixActualBandLocalFirstJetContribution,
    suffixActualBandLocalRouteEndpointDefect,
    suffixActualBandLocalPolarJuliaContribution,
    suffixActualBandLocalRoutePolarOrderingResidual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, map_sub, smul_sub]
  abel

/-! ## The genuine polar Julia slot -/

/-- The right factor left after extracting the canonical left Julia
co-defect from the polar contribution. -/
noncomputable def suffixActualBandLocalPolarJuliaRightFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  ((suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor.factor)† ∘L
    detectorOperator owner ∘L newSuffixFrame lambda S ∘L
      suffixEulerFrameReverseTransition lambda p S

/-- The polar contribution is genuinely supported in the actual left Julia
co-defect of this adjacent-frame step. -/
theorem suffixActualBandLocalPolarJuliaContribution_eq_leftCoDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalPolarJuliaContribution owner lambda p S =
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
        suffixActualBandLocalPolarJuliaRightFactor owner lambda p S := by
  rw [suffixActualBandLocalPolarJuliaContribution,
    suffixEulerDetectorRelativeNumerator_eq_boundary_comp_reverse,
    suffixEulerDetectorBoundaryDefect_eq_juliaCoDefect]
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandLocalPolarJuliaRightFactor,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, neg_neg]

/-! ## Exact non-polar localization gap -/

/-- Everything not yet known to lie in the same Julia co-defect: the local
first jet and the route/polar ordering residual are kept together. -/
noncomputable def suffixActualBandLocalNonpolarLocalizationGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandLocalFirstJetContribution owner lambda p S +
    suffixActualBandLocalRoutePolarOrderingResidual owner lambda p S

/-- The full local raw defect is the proved polar Julia term plus exactly one
unresolved non-polar gap. -/
theorem suffixActualBandLocalRawDefect_eq_polarJulia_add_nonpolarGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRawDefect owner lambda p S =
      suffixActualBandLocalPolarJuliaContribution owner lambda p S +
        suffixActualBandLocalNonpolarLocalizationGap owner lambda p S := by
  rw [suffixActualBandLocalRawDefect_eq_signedLocalization]
  simp only [suffixActualBandLocalNonpolarLocalizationGap]
  abel

/-- Full localization through the current Julia slot is equivalent to one
source theorem for the non-polar gap.  This equivalence does not assert that
such a right factor exists. -/
theorem suffixActualBandLocalRawDefect_eq_leftCoDefect_iff_nonpolarGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (completion : SourceOp lambda) :
    suffixActualBandLocalRawDefect owner lambda p S =
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
          (suffixActualBandLocalPolarJuliaRightFactor owner lambda p S +
            completion) <->
      suffixActualBandLocalNonpolarLocalizationGap owner lambda p S =
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L completion := by
  have hpolar :=
    suffixActualBandLocalPolarJuliaContribution_eq_leftCoDefect
      owner lambda p S
  have hsplit :=
    suffixActualBandLocalRawDefect_eq_polarJulia_add_nonpolarGap
      owner lambda p S
  constructor
  · intro hfull
    calc
      suffixActualBandLocalNonpolarLocalizationGap owner lambda p S =
          suffixActualBandLocalRawDefect owner lambda p S -
            suffixActualBandLocalPolarJuliaContribution owner lambda p S := by
              rw [hsplit]
              abel
      _ = ((suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
              (suffixActualBandLocalPolarJuliaRightFactor owner lambda p S +
                completion)) -
            ((suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
              suffixActualBandLocalPolarJuliaRightFactor owner lambda p S) := by
                rw [hfull, hpolar]
      _ = (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
          completion := by
            apply ContinuousLinearMap.ext
            intro x
            simp only [ContinuousLinearMap.comp_apply,
              ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
              map_add]
            abel
  · intro hgap
    calc
      suffixActualBandLocalRawDefect owner lambda p S =
          suffixActualBandLocalPolarJuliaContribution owner lambda p S +
            suffixActualBandLocalNonpolarLocalizationGap owner lambda p S :=
        hsplit
      _ = ((suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
              suffixActualBandLocalPolarJuliaRightFactor owner lambda p S) +
            ((suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
              completion) := by rw [hpolar, hgap]
      _ = (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
          (suffixActualBandLocalPolarJuliaRightFactor owner lambda p S +
            completion) := by
              apply ContinuousLinearMap.ext
              intro x
              simp only [ContinuousLinearMap.comp_apply,
                ContinuousLinearMap.add_apply, map_add]

/-! ## Suffix-scaled local decomposition -/

/-- The polar Julia contribution with the exact suffix scalar kept on the
right, matching the recursive relative-numerator product. -/
noncomputable def suffixActualBandLocalScaledPolarJuliaContribution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  -(suffixEulerDetectorRelativeNumerator owner lambda p S ∘L
    suffixEulerSchurMarkovScaleOperator lambda S)

/-- The local increment of the scaled route/polar ordering defect. -/
noncomputable def suffixActualBandLocalScaledRoutePolarOrderingResidual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixEulerDetectorRelativeNumerator owner lambda p S ∘L
      suffixEulerSchurMarkovScaleOperator lambda S -
    suffixActualBandLocalEndpointDefect owner lambda p S

/-- The existing scaled first-jet defect is exactly the suffix scalar times
the unscaled first-jet contribution. -/
theorem suffixActualBandLocalFirstJetDefect_eq_suffixScalar_smul
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalFirstJetDefect owner lambda p S =
      (suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandLocalFirstJetContribution owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandLocalFirstJetDefect,
    suffixActualBandLocalFirstJetContribution,
    suffixEulerSchurMarkovScalar, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    map_smul, smul_sub, smul_smul]
  push_cast
  rw [mul_comm (primeSchurMarkovScalar p : ℂ)
    (suffixEulerSchurMarkovScalar S : ℂ)]

/-- The existing scaled endpoint defect is exactly the suffix scalar times
the unscaled route endpoint defect. -/
theorem suffixActualBandLocalEndpointDefect_eq_suffixScalar_smul
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalEndpointDefect owner lambda p S =
      (suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandLocalRouteEndpointDefect owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandLocalEndpointDefect,
    suffixActualBandLocalRouteEndpointDefect,
    suffixEulerSchurMarkovScalar, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    map_smul, smul_sub, smul_smul]
  push_cast
  rw [mul_comm (primeSchurMarkovScalar p : ℂ)
    (suffixEulerSchurMarkovScalar S : ℂ)]

/-- The right scalar operator is definitionally the same suffix scaling of
the unscaled polar Julia contribution. -/
theorem suffixActualBandLocalScaledPolarJuliaContribution_eq_suffixScalar_smul
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalScaledPolarJuliaContribution owner lambda p S =
      (suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandLocalPolarJuliaContribution owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandLocalScaledPolarJuliaContribution,
    suffixActualBandLocalPolarJuliaContribution,
    suffixEulerSchurMarkovScaleOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.neg_apply, map_smul, smul_neg]

/-- The scaled ordering increment is exactly the suffix scalar times the
unscaled route/polar ordering residual. -/
theorem suffixActualBandLocalScaledRoutePolarOrderingResidual_eq_suffixScalar_smul
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalScaledRoutePolarOrderingResidual owner lambda p S =
      (suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandLocalRoutePolarOrderingResidual owner lambda p S := by
  rw [suffixActualBandLocalScaledRoutePolarOrderingResidual,
    suffixActualBandLocalEndpointDefect_eq_suffixScalar_smul]
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandLocalRoutePolarOrderingResidual,
    suffixEulerSchurMarkovScaleOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.sub_apply, map_smul, smul_sub]

/-- The existing local completed defect has the same signed three-part
decomposition with all suffix scaling kept inside the operators. -/
theorem suffixActualBandLocalCompletedDefect_eq_scaledSignedLocalization
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalCompletedDefect owner lambda p S =
      suffixActualBandLocalFirstJetDefect owner lambda p S +
        suffixActualBandLocalScaledPolarJuliaContribution owner lambda p S +
          suffixActualBandLocalScaledRoutePolarOrderingResidual
            owner lambda p S := by
  rw [suffixActualBandLocalCompletedDefect_eq_firstJet_sub_endpoint]
  simp only [suffixActualBandLocalScaledPolarJuliaContribution,
    suffixActualBandLocalScaledRoutePolarOrderingResidual]
  abel

/-! ## Global ordering-defect recurrence -/

/-- List-level route/polar ordering difference before specializing to a
`FinitePrimePowerFamily`. -/
noncomputable def suffixActualBandRoutePolarOrderingDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixEulerDetectorRelativeNumeratorProduct owner lambda S -
    (suffixEulerSchurMarkovScalar S : ℂ) •
      suffixActualBandEndpointCycledResponse owner lambda S

/-- The scaled local residual is exactly the inhomogeneous term in the
one-step recurrence of the global route/polar ordering defect. -/
theorem suffixActualBandRoutePolarOrderingDefect_cons
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRoutePolarOrderingDefect owner lambda (p :: S) =
      suffixEulerFrameTransition lambda p S ∘L
          suffixActualBandRoutePolarOrderingDefect owner lambda S ∘L
            suffixEulerFrameReverseTransition lambda p S +
        suffixActualBandLocalScaledRoutePolarOrderingResidual
          owner lambda p S := by
  rw [suffixActualBandRoutePolarOrderingDefect,
    suffixEulerDetectorRelativeNumeratorProduct_cons,
    suffixActualBandLocalScaledRoutePolarOrderingResidual,
    suffixActualBandLocalEndpointDefect]
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandRoutePolarOrderingDefect,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_sub]
  abel

/-- The arbitrary-list endpoint specializes to the existing actual endpoint
for a finite prime-power family. -/
theorem suffixActualBandEndpointCycledResponse_eq_actual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandEndpointCycledResponse owner lambda family.visiblePrimes =
      actualBandEndpointCycledResponse owner lambda family := by
  rw [suffixActualBandEndpointCycledResponse,
    actualBandEndpointCycledResponse,
    suffixActualBandTargetFrameRootLeg_eq_actual,
    suffixActualBandTargetDualRootLeg_eq_actual]

/-- On the arithmetic visible-prime list, the list-level ordering difference
is the existing ordering defect used by the corrected signed cocycle. -/
theorem suffixActualBandRoutePolarOrderingDefect_eq_existing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandRoutePolarOrderingDefect owner lambda
        family.visiblePrimes =
      suffixEulerScaledPolarOrderingDefect owner lambda family := by
  rw [suffixActualBandRoutePolarOrderingDefect,
    suffixEulerScaledPolarOrderingDefect,
    suffixActualBandEndpointCycledResponse_eq_actual,
    sourceBandGramResponse_eq_endpointCycle]

end CCM24FiniteSCompletedJuliaSignedLocalization
end CCM25Concrete
end Source
end ConnesWeilRH
