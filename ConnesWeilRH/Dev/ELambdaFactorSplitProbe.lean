import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
import ConnesWeilRH.Dev.ELambdaProjectorNormBoundProbe

/-!
# Factor = Q_λ ∘ B_λ: generic-λ spectral content is the band compression B_λ Q_λ B_λ

`ELambdaProjectorNormBoundProbe` (852) read the source prolate factor as three
projections `Q_λ (E_λ - R₀_λ)` and got the crude ceiling `‖factor λ‖ ≤ 1·2 = 2`.

But the repo already proves a stronger structural fact
(`sourceBandProjection_isStarProjection`): the band `B_λ := E_λ - R₀_λ` is its
own orthogonal star-projection, so `‖B_λ‖ ≤ 1`. Since the factor is literally
`Q_λ ∘ B_λ`, the two-factor split `‖Q_λ∘B_λ‖ ≤ ‖Q_λ‖·‖B_λ‖ ≤ 1` improves 852's
ceiling from `≤ 2` to `≤ 1`.

The generic-λ Hilbert-Schmidt summability gate
`sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong` reduces to
`PositiveTrace.IsTraceClassAlong globalBasis (sourceProlateRemainder λ)`, and
`sourceProlateRemainder λ = B_λ Q_λ B_λ`.  Factor this through the band carrier:
with `j := sourceBandInclusion λ` (isometric inclusion of `range B_λ`,
`j†∘j = id`, `j∘j† = B_λ`),

    B_λ Q_λ B_λ = j ∘ (j† Q_λ j) ∘ j†

so the spectrum/eigenvalue-decay of the remainder is exactly that of the band
compression `A := j† Q_λ j : sourceBandCarrier λ →L ℂ sourceBandCarrier λ`.

RH is NOT claimed. Zero `sorry`; axiom-clean.
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
open scoped InnerProduct

noncomputable local instance sourceBandCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceBandCarrier lambda) :=
  (sourceBandClosedRange lambda).isClosed.completeSpace_coe

/-- The factor is literally `Q_λ ∘ B_λ` with `B_λ = E_λ - R₀_λ`. -/
lemma factor_eq_band_comp (lambda : CCM24SoninScale) :
    sourceProlateHilbertSchmidtFactor lambda =
      sourceFourierSupportProjection lambda ∘L sourceBandProjection lambda := by
  unfold sourceProlateHilbertSchmidtFactor sourceBandProjection
  rfl

/-- Strengthen 852: the source prolate factor has operator norm ≤ 1, because
the band `B_λ` and `Q_λ` are orthogonal projections (each `‖·‖ ≤ 1`). -/
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

/-- The generic-λ remainder is `B_λ Q_λ B_λ`: the positive square of the factor
collapses by self-adjoint idempotence (`remainder = factor† factor`,
`factor = Q_λ∘B_λ`, `Q_λ`, `B_λ` idempotent).  This is the sharp dock: generic-λ
`Summable` holds iff `B_λ Q_λ B_λ` is trace-class along the basis. -/
lemma remainder_eq_band_comp_band (lambda : CCM24SoninScale) :
    sourceProlateRemainder lambda =
      sourceBandProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
        sourceBandProjection lambda := by
  simpa [sourceBandProjection] using sourceProlateRemainder_eq_factor lambda

/-- Step 1 (band compression): compose the remainder with the band isometry
`j = sourceBandInclusion λ`.  Via `j∘j† = B_λ` (always rewrite B_λ to j∘j†)
and `j†∘j = id`:
    j† (B_λ Q_λ B_λ) j = j† Q_λ j
So the generic-λ spectral content of the remainder is exactly the band-Fourier
compression `A := j† Q_λ j : (sourceBandCarrier λ) →L[ℂ] (sourceBandCarrier λ)`,
restricted to `range B_λ`.  This is the operator the A-lane must show is
trace-class (= generic-λ `Summable`). -/
lemma adjoint_bandProjection (lambda : CCM24SoninScale) :
    (sourceBandInclusion lambda)† ∘L sourceBandProjection lambda =
      (sourceBandInclusion lambda)† := by
  --  j† = j† (j j†) = (j† j) j† = id j† = j†
  rw [← sourceBandInclusion_comp_adjoint lambda]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [sourceBandInclusion_adjoint_comp_self lambda]
  simp

/-- The band compression `A = j† Q_λ j` on `sourceBandCarrier λ`: the operator
whose eigenvalue-decay (: trace-class on `range B_λ`) is exactly the generic-λ
spectral content of the remainder.  Step 1 asserts the remainder's band
compression equals the band-Fourier compression:
`j† (B Q B) j = j† Q j`, killing `j†∘B = j†` on the left and `B∘j = j` on the
right (proved pointwise: `ext` then `comp_apply`, then both band factors
collapse).  Notation: `j = sourceBandInclusion λ`, `B = sourceBandProjection λ`,
`Q = sourceFourierSupportProjection λ`. -/
lemma band_compression_eq (lambda : CCM24SoninScale) :
    (sourceBandInclusion lambda)† ∘L sourceProlateRemainder lambda ∘L
        sourceBandInclusion lambda =
      (sourceBandInclusion lambda)† ∘L sourceFourierSupportProjection lambda ∘L
        sourceBandInclusion lambda := by
  rw [remainder_eq_band_comp_band lambda]
  apply ContinuousLinearMap.ext
  intro u
  --  pointwise:   j† (B Q B (j u)) = j† (Q (j u)).
  simp only [ContinuousLinearMap.comp_apply]
  --  inner band factor:  B (j u) = j u
  have hB : sourceBandProjection lambda (sourceBandInclusion lambda u) =
      sourceBandInclusion lambda u := by
    exact DFunLike.congr_fun (sourceBandProjection_comp_sourceBandInclusion lambda) u
  rw [hB]  --  -> j† (B Q (j u)) = j† (Q (j u))
  --  outer band factor, at the vector Q(j u):  (j† ∘ B) = j†
  have hO : ContinuousLinearMap.adjoint (sourceBandInclusion lambda)
        (sourceBandProjection lambda
          (sourceFourierSupportProjection lambda (sourceBandInclusion lambda u))) =
      ContinuousLinearMap.adjoint (sourceBandInclusion lambda)
        (sourceFourierSupportProjection lambda (sourceBandInclusion lambda u)) := by
    exact DFunLike.congr_fun (adjoint_bandProjection lambda)
      (sourceFourierSupportProjection lambda (sourceBandInclusion lambda u))
  exact hO

end ELambdaFactorProbe
end CC20Concrete
end Source
end ConnesWeilRH