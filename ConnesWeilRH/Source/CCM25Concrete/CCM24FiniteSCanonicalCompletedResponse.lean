/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandCompletedNumerator
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalEulerEnergy

/-!
# Canonical-family specialization of the completed band response

The selected Weil square already determines the exact prime-power family used
by the semilocal carrier.  This module specializes the completed numerator and
its inverse-Gram response to that same family, so the algebraic ledger and the
support-only mode budget refer to one object.  It does not assert a bound for
the completed trace: the energy-to-boundary estimate remains the open Gate 3U
producer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCanonicalCompletedResponse

open CC20Concrete
open SelectedWeilSquare
open CCM24FiniteSProjectionTrace
open CCM24FiniteSProjectionTrace.FinitePrimePowerFamily
open CCM24FiniteSActualBandCompletedNumerator
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSGramResponse
open CCM24FiniteSOrderedCausalGram
open CCM24FiniteSCanonicalEulerEnergy

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (CCM24FiniteSGramResponse.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The exact finite-S family selected by one compact Weil square. -/
noncomputable def canonicalFamily
    (owner : SelectedWeilSquareOwner) : FinitePrimePowerFamily :=
  ofSelectedOwner owner

/-- The completed relative numerator on the canonical selected family. -/
noncomputable def canonicalActualBandCompletedRelativeNumerator
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSGramResponse.sourceSoninCarrier lambda :=
  actualBandCompletedRelativeNumerator owner lambda (canonicalFamily owner)

/-- The canonical inverse-Gram completed response. -/
noncomputable def canonicalActualBandCompletedRelativeResponse
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSGramResponse.sourceSoninCarrier lambda :=
  actualBandCompletedRelativeResponse owner lambda (canonicalFamily owner)

/-- The source remainder reads back as the canonical quadratic cycle, with no
arbitrary-family parameter left in the statement. -/
theorem canonicalSourceRemainder_eq_canonicalQuadraticCycle
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    sourceActualBandFiniteEulerRemainderResponse owner lambda
        (canonicalFamily owner) =
      actualBandQuadraticCycledResponse owner lambda (canonicalFamily owner) := by
  exact sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle
    owner lambda (canonicalFamily owner)

/-- The canonical completed numerator is the quadratic cycle followed by the
same canonical Gram covariance. -/
theorem canonicalActualBandCompletedRelativeNumerator_eq_quadraticCycle_comp_gamma
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    canonicalActualBandCompletedRelativeNumerator owner lambda =
      actualBandQuadraticCycledResponse owner lambda (canonicalFamily owner) ∘L
        sourceOrderedCausalGamma lambda (canonicalFamily owner) := by
  exact actualBandCompletedRelativeNumerator_eq_quadraticCycle_comp_gamma
    owner lambda (canonicalFamily owner)

/-- Applying the canonical inverse Gram covariance produces the canonical
quadratic cycle exactly. -/
theorem canonicalActualBandCompletedRelativeNumerator_comp_gammaInv_eq_quadraticCycle
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    canonicalActualBandCompletedRelativeNumerator owner lambda ∘L
        sourceOrderedCausalGammaInv lambda (canonicalFamily owner) =
      actualBandQuadraticCycledResponse owner lambda (canonicalFamily owner) := by
  exact actualBandCompletedRelativeNumerator_comp_gammaInv_eq_quadraticCycle
    owner lambda (canonicalFamily owner)

/-- The canonical source remainder is the completed inverse-Gram response on
the same selected family. -/
theorem canonicalSourceRemainder_eq_canonicalCompletedResponse
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    sourceActualBandFiniteEulerRemainderResponse owner lambda
        (canonicalFamily owner) =
      canonicalActualBandCompletedRelativeResponse owner lambda := by
  exact sourceActualBandFiniteEulerRemainderResponse_eq_completedRelativeResponse
    owner lambda (canonicalFamily owner)

/-- The genuine synchronized mode energy for the same canonical family has a
support-radius-only polynomial bound. -/
theorem canonicalModeEnergy_le_supportRadiusPolynomial
    (owner : SelectedWeilSquareOwner) :
    canonicalSynchronizedEulerModeEnergy owner ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) :=
  canonicalSynchronizedEulerModeEnergy_le_supportRadiusPolynomial owner

end CCM24FiniteSCanonicalCompletedResponse
end CCM25Concrete
end Source
end ConnesWeilRH
