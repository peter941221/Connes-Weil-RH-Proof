import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace

/-!
# Sharp prolate-factor norm ‖factor‖ ≤ 1

`sourceProlateHilbertSchmidtFactor lambda = sourceFourierSupportProjection lambda
<= (radialSupportProjection lambda - sourceSoninProjection lambda)`
(CCM24SourceProlateTrace:35).  The second factor is the source *band*
`B0 = radial - sourceSonin`, which is an orthogonal (star) projection
(CCM24FiniteSFixedQuotientCarrier:46), hence of norm ≤ 1; the first factor is
an orthogonal projection too, norm ≤ 1.  Composition gives

    ‖factor‖ <= ‖fourier‖ * ‖B0‖ ≤ 1 * 1 = 1.

This sharpens the coarse triangle-inequality ceiling `‖B0‖ <= 2` recorded in
`ELambdaProjectorNormBoundProbe` (2026-08-06) to a strict notion: the prolate
factor itself has operator norm ≤ 1.  It does NOT supply the strict
contraction `‖factor‖ < 1` required for `Summable ‖factor‖^2` from the
operator-norm route alone (the spectral/eigenvalue route is still required),
and it does NOT close the infinite-carrier Gate. RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Dev
namespace ProlateFactorNorm

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier

/-- The prolate factor `Q_0 (E-R_0)` has operator norm ≤ 1. -/
theorem prolateFactor_norm_le_one (lambda : CCM24SoninScale) :
    ‖sourceProlateHilbertSchmidtFactor lambda‖ ≤ 1 := by
  have hA : ‖sourceFourierSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceFourierSupportProjection_isStarProjection lambda)
  have hB : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hfac : sourceProlateHilbertSchmidtFactor lambda =
      sourceFourierSupportProjection lambda ∘L sourceBandProjection lambda := by
    rfl
  calc
    ‖sourceProlateHilbertSchmidtFactor lambda‖ <=
        ‖sourceFourierSupportProjection lambda‖ * ‖sourceBandProjection lambda‖ := by
      rw [hfac]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by exact mul_le_mul hA hB (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

end ProlateFactorNorm
end Dev
end ConnesWeilRH
