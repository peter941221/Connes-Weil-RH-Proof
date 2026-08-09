import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
import ConnesWeilRH.Dev.ELambdaProjectorNormBoundProbe

/-!
# Factor = Q_λ ∘ B_λ: generic-λ spectral content is the band compression B_λ Q_λ B_λ

`ELambdaProjectorNormBoundProbe` (852) read the source prolate factor as three
projections `Q_λ (E_λ - R₀_λ)` and got the crude ceiling `‖factor λ‖ ≤ 1·2 = 2`.

But the repo already proves a stronger structural fact
(`sourceBandProjection_isStarProjection`, `CCM24FiniteSFixedQuotientCarrier`):
the band `B_λ := E_λ - R₀_λ` is its own orthogonal star-projection, so
`‖B_λ‖ ≤ 1`. Since the factor is literally `Q_λ ∘ B_λ`, the two-factor split

    ‖factor λ‖ = ‖Q_λ ∘ B_λ‖ ≤ ‖Q_λ‖ · ‖B_λ‖ ≤ 1 · 1 = 1

improves 852's ceiling from `≤ 2` to `≤ 1`.

And because `sourceProlateRemainder λ = (factor λ)† (factor λ) = B_λ Q_λ B_λ`,
the generic-λ Hilbert-Schmidt summability gate `Summable ‖factor(s)‖²` reduces
exactly to the trace-classity of `B_λ Q_λ B_λ` on range B_λ. That is the precise
A-lane docking statement. RH is NOT claimed. Zero `sorry`; axiom-clean.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace ELambdaFactorProbe

open MeasureTheory Set
open ELambdaNormBound
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier

/-- The factor is literally `Q_λ ∘ B_λ` with `B_λ = E_λ - R₀_λ`. -/
lemma factor_eq_band_comp (lambda : CCM24SoninScale) :
    sourceProlateHilbertSchmidtFactor lambda =
      sourceFourierSupportProjection lambda ∘L sourceBandProjection lambda := by
  unfold sourceProlateHilbertSchmidtFactor sourceBandProjection
  rfl

/-- Strengthen 852: the source prolate factor has operator norm ≤ 1, because
the band `B_λ` is an orthogonal projection (so ‖B_λ‖ ≤ 1) and `Q_λ` is one. -/
lemma factor_norm_le_one (lambda : CCM24SoninScale) :
    ‖sourceProlateHilbertSchmidtFactor lambda‖ ≤ 1 := by
  rw [factor_eq_band_comp lambda]
  have hQ : ‖sourceFourierSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceFourierSupportProjection_isStarProjection lambda)
  have hB : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hcomp : ‖sourceFourierSupportProjection lambda ∘L sourceBandProjection lambda‖ ≤
      ‖sourceFourierSupportProjection lambda‖ * ‖sourceBandProjection lambda‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖sourceFourierSupportProjection lambda ∘L sourceBandProjection lambda‖ ≤
        ‖sourceFourierSupportProjection lambda‖ * ‖sourceBandProjection lambda‖ := hcomp
    _ ≤ 1 * ‖sourceBandProjection lambda‖ := by
          exact mul_le_mul hQ (le_refl _) (norm_nonneg _) (by norm_num)
    _ ≤ 1 * (1 : ℝ) := by
          exact mul_le_mul (le_refl (1 : ℝ)) hB (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- The generic-λ remainder is `B_λ Q_λ B_λ` on the band carrier: by
`sourceProlateHilbertSchmidtFactor_adjoint_comp_self` the remainder is
`factor† factor`, and with `factor = Q_λ ∘ B_λ` (B_λ self-adjoint idempotent)
the positive square collapses to `B_λ Q_λ B_λ`.  This pins the A-lane gate: the
generic-λ `Summable` holds iff `B_λ Q_λ B_λ` is trace-class along the basis. -/
lemma remainder_eq_band_comp_band (lambda : CCM24SoninScale) :
    sourceProlateRemainder lambda =
      sourceBandProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
        sourceBandProjection lambda := by
  simpa [sourceBandProjection] using sourceProlateRemainder_eq_factor lambda

end ELambdaFactorProbe
end CC20Concrete
end Source
end ConnesWeilRH