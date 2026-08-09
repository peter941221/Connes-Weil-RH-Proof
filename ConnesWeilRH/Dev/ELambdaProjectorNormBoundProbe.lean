import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20YoshidaMellin
import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Dev.SchwartzAmbientOwnerProbe
import ConnesWeilRH.Source.CC20Concrete.CCM24LogRadialSupport
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Dev.ELambdaFamilyMonotoneProbe
import ConnesWeilRH.Dev.ELambdaFamilyProjectorProbe

/-!
# The prolate factor is not a strict contraction: `‖factor λ‖ ≤ 2`

`ELambdaFamilyProjectorProbe` (851) proved the projector-family folding
identity.  The remaining step toward generic-λ `Summable ‖factor λ‖²` is the
spectral estimate.  This probe records the *structural obstruction* to the
easiest route:

    factor λ = Q_λ ∘ (E_λ − R₀_λ),
    each of Q_λ, E_λ, R₀_λ is an orthogonal projection with `‖ · ‖ ≤ 1`.

Hence `‖factor λ‖ ≤ ‖Q_λ‖ · ‖E_λ − R₀_λ‖ ≤ 1 · 2 = 2`.  In particular the
strict-contraction hypothesis `‖factor λ‖ < 1` that the generic summable
theorem (`summable_normSq_of_strictContraction_of_defect`, HilbertSchmidtIdeal
:293) and its Route-C versions demand CANNOT be furnished from the projection
structure alone: the operator-norm ceiling is 2, not < 1.  So the remaining
generic-λ gap is necessarily *spectral* (eigenvalue decay), not an operator
norm `< 1` shortcut.  That is the honest content of the wall 839-848 kept
pointing at, now stated as a Lean-verified bound.

The bound itself is axiom-clean and new.  It does NOT give `Summable`; it
documents why the strict-contraction route is closed so the spectral route is
the only one left.  RH is NOT claimed.  Zero `sorry`.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace ELambdaNormBound

open MeasureTheory Set
open ELambdaMonotone
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace

/-- The radial-support difference `E_λ - R₀_λ` has norm at most `2`. -/
lemma radialSoninDifference_norm_le_two
    (lambda : CCM24SoninScale) :
    ‖radialSupportProjection lambda - sourceSoninProjection lambda‖ ≤ 2 := by
  have hE : ‖radialSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (radialSupportProjection_isStarProjection lambda)
  have hR : ‖sourceSoninProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection lambda)
  have htri : ‖radialSupportProjection lambda - sourceSoninProjection lambda‖ ≤
      ‖radialSupportProjection lambda‖ + ‖sourceSoninProjection lambda‖ :=
    norm_sub_le _ _
  linarith

/-- The source prolate factor has operator norm ≤ 2: three projections. -/
lemma prolateFactor_norm_le_two
    (lambda : CCM24SoninScale) :
    ‖sourceProlateHilbertSchmidtFactor lambda‖ ≤ 2 := by
  have hQ : ‖sourceFourierSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceFourierSupportProjection_isStarProjection lambda)
  have hdiff : ‖radialSupportProjection lambda - sourceSoninProjection lambda‖ ≤ 2 :=
    radialSoninDifference_norm_le_two lambda
  have hcomp_le : ‖sourceProlateHilbertSchmidtFactor lambda‖ ≤
      ‖sourceFourierSupportProjection lambda‖ *
        ‖radialSupportProjection lambda - sourceSoninProjection lambda‖ := by
    -- ‖A ∘ B‖ ≤ ‖A‖ · ‖B‖ (the factor IS the composition)
    unfold sourceProlateHilbertSchmidtFactor
    exact ContinuousLinearMap.opNorm_comp_le _
        (radialSupportProjection lambda - sourceSoninProjection lambda)
  calc
    ‖sourceProlateHilbertSchmidtFactor lambda‖ ≤
        ‖sourceFourierSupportProjection lambda‖ *
          ‖radialSupportProjection lambda - sourceSoninProjection lambda‖ :=
      hcomp_le
    _ ≤ 1 * 2 := by
          exact mul_le_mul hQ hdiff (norm_nonneg _) (by norm_num)
    _ = 2 := by ring

end ELambdaNormBound
end CC20Concrete
end Source
end ConnesWeilRH