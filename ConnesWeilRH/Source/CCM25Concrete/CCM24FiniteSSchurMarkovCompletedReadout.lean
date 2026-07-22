/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovPairing
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawCompletedGaugeOwner

/-!
# Completed signed Schur--Markov readout

The polar Schur--Markov cocycle and the ordered Gram endpoint use different
operator orderings.  Infinite-dimensional trace cyclicity cannot be used to
identify them: doing so would delete the trace anomaly retained by the actual
finite-S response.

This module keeps their difference as an explicit scaled ordering defect and
recombines it with the complete physical first jet.  The resulting operator is
exactly the positive Schur--Markov scalar times the existing lower-factor-
gauged completed response.  The outer, reflected, second-support, and prolate
branches remain inside the existing physical operators throughout.

No uniform estimate, sign theorem, Gate 3U conclusion, or RH premise is
introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSchurMarkovCompletedReadout

open scoped InnerProduct

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-- The difference between the actual polar signed numerator and the same
positive scalar times the route-ordered Gram endpoint.  This is the ordering
term which must remain until a source-specific trace-anomaly theorem controls
it. -/
noncomputable def suffixEulerScaledPolarOrderingDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  suffixEulerDetectorRelativeNumeratorProduct owner lambda
      family.visiblePrimes -
    (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
      sourceBandGramResponse owner lambda family

/-- The complete signed owner.  The physical first jet remains whole, the
polar endpoint is the complete signed cocycle, and the exact ordering defect
is restored before any trace or norm is taken. -/
noncomputable def suffixEulerLowerFactorCompletedSignedCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
      actualBandFirstJetCycledResponse owner lambda family -
    suffixEulerDetectorRelativeNumeratorProduct owner lambda
      family.visiblePrimes +
    suffixEulerScaledPolarOrderingDefect owner lambda family

/-- The completed owner uses the recursive signed telescope, not a sum of
primewise absolute values. -/
theorem suffixEulerLowerFactorCompletedSignedCocycle_eq_telescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerLowerFactorCompletedSignedCocycle owner lambda family =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
          actualBandFirstJetCycledResponse owner lambda family -
        suffixEulerDetectorSignedCocycle owner lambda family.visiblePrimes +
        suffixEulerScaledPolarOrderingDefect owner lambda family := by
  rw [suffixEulerLowerFactorCompletedSignedCocycle,
    suffixEulerDetectorSignedCocycle_eq_relativeNumeratorProduct]

/-- Exact same-object readback to the lower-factor-gauged completed response.
The ordering defect is retained, so this theorem uses no trace cycle. -/
theorem suffixEulerLowerFactorCompletedSignedCocycle_eq_scaledResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerLowerFactorCompletedSignedCocycle owner lambda family =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
        lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family := by
  rw [suffixEulerLowerFactorCompletedSignedCocycle,
    suffixEulerScaledPolarOrderingDefect,
    lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder,
    sourceActualBandFiniteEulerRemainderResponse,
    sourceActualBandFiniteEulerSoninResponse_eq_firstJetCycle]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_sub]
  abel

/-- The scaling in the completed readout is nonzero for every finite visible
prime list. -/
theorem suffixEulerCompletedReadoutScale_ne_zero
    (family : FinitePrimePowerFamily) :
    (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt (suffixEulerSchurMarkovScalar_pos family.visiblePrimes))

/-- Fixed-family trace legality transfers from the existing completed
response to the corrected signed cocycle by the exact operator identity. -/
theorem suffixEulerLowerFactorCompletedSignedCocycle_isTraceClassAlong
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hresponse : IsTraceClassAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)) :
    IsTraceClassAlong sourceBasis
      (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family) := by
  rw [suffixEulerLowerFactorCompletedSignedCocycle_eq_scaledResponse]
  exact isTraceClassAlong_smul sourceBasis _ _ hresponse

/-- The ordinary trace of the complete corrected cocycle is the literal
positive scalar times the existing lower-factor-gauged response trace. -/
theorem ordinaryTraceAlong_suffixEulerCompletedSignedCocycle_eq_scaledResponse
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hresponse : IsTraceClassAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)) :
    ordinaryTraceAlong sourceBasis
        (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family) =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) *
        ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family) := by
  rw [suffixEulerLowerFactorCompletedSignedCocycle_eq_scaledResponse]
  exact ordinaryTraceAlong_smul sourceBasis _ _ hresponse

end CCM24FiniteSSchurMarkovCompletedReadout
end CCM25Concrete
end Source
end ConnesWeilRH
