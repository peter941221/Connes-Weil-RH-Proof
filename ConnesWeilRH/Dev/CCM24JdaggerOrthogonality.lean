import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawRemainderCommonPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse

/-!
# The J-dual and the Sonin-dual of the finite-band forward coframe vanish

The infinite-carrier Gate (docs/928, 931) is the operator identity

    Gate31_bottom :  B o N^-1 o J  +  H o J o G^-1  =  J

with B = sourceBandProjection = radial - P,  N = normalized transport inverse,
J = sourceInclusion, H = ambient Gram, G = restricted Gram, P = sourceSoninProjection.

This module proves BOTH projection-adjoint annihilations of the forward block
M := B o N^-1 o J  by Leibniz algebra (no analysis):

  * J-dagger o M = 0     (inclusion adjoint;  docs/932)
  * P          o M = 0   (Sonin projection, this module)

Facts used (in-repo, axiom-clean):
  J-dagger = J-dagger o P              (sourceInclusionAdjoint_comp_sourceProjection)
  P o B = 0                             (sourceSoninProjection_comp_sourceBandProjection_eq_zero)

=>
  J-dagger o B = 0                       (from first)
  P o C = P o (B o N^-1 o J) = (P o B) o (N^-1 o J) = 0
  J-dagger o C = (J-dagger o B) o (N^-1 o J) = 0

It does NOT close the Gate: it shows the residual information lives only in the
operator norm of the (E-P) projection of M, which still requires analysis.
RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Dev
namespace BandJdaggerZero

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Source.CCM25Concrete
open scoped InnerProduct
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawRemainderCommonPair
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInverseMetric
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The band projection is orthogonal to the Sonin inclusion dual: J^dagger o B = 0. -/
theorem inclusionAdjoint_comp_band_eq_zero (lambda : CCM24SoninScale) :
    (sourceInclusion lambda)† ∘L sourceBandProjection lambda = 0 := by
  rw [← sourceInclusionAdjoint_comp_sourceProjection lambda]
  rw [ContinuousLinearMap.comp_assoc]
  rw [sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda]
  simp

/-- The Sonin projection annihilates the forward band coframe: P o B o N^-1 o J = 0. -/
theorem sonin_comp_forwardBandCoframe_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L sourceActualBandForwardCoframe lambda family = 0 := by
  rw [sourceActualBandForwardCoframe]
  apply ContinuousLinearMap.ext
  intro u
  change sourceSoninProjection lambda
      (sourceBandProjection lambda
        (normalizedFiniteEulerInverse family (sourceInclusion lambda u))) = 0
  have h := congrFun (congrArg DFunLike.coe
    (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda))
    (normalizedFiniteEulerInverse family (sourceInclusion lambda u))
  simpa using h

/-- The dagger-dual of the forward band coframe M = B o N^-1 o J vanishes. -/
theorem dagger_comp_forwardBandCoframe_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L sourceActualBandForwardCoframe lambda family = 0 := by
  rw [sourceActualBandForwardCoframe]
  apply ContinuousLinearMap.ext
  intro u
  change ContinuousLinearMap.adjoint (sourceInclusion lambda)
      (sourceBandProjection lambda
        (normalizedFiniteEulerInverse family (sourceInclusion lambda u))) = 0
  have h := congrFun (congrArg DFunLike.coe
    (inclusionAdjoint_comp_band_eq_zero lambda))
    (normalizedFiniteEulerInverse family (sourceInclusion lambda u))
  simpa using h

end BandJdaggerZero
end Dev
end ConnesWeilRH
