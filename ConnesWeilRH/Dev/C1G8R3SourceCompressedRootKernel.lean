/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3GateAmbientNormalForm

set_option maxHeartbeats 2000000

/-!
# Direct source-compressed root kernel

This leaf starts the direct-kernel route for S3.  The source-compressed root
is treated as a rectangular operator on the actual Sonin carrier; its matrix
coefficients are pulled back to the ambient root without introducing an
ambient Hilbert--Schmidt premise.  The coefficient identity is the exact
starting point for a future source-carrier kernel estimate.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProductSpace

local notation "Carrier" => finiteSCarrier

noncomputable local instance sourceCompressedRootCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable def sourceCompressedRoot
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
    sourceInclusion lambda

/-- The source-compressed root coefficient is the ambient root coefficient
after inserting the same source inclusion on both sides. -/
theorem sourceCompressedRoot_inner_eq_ambient
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (u v : sourceSoninCarrier lambda) :
    inner ℂ (sourceCompressedRoot owner lambda u) v =
      inner ℂ (rootConvolution owner (sourceInclusion lambda u))
        (sourceInclusion lambda v) := by
  unfold sourceCompressedRoot
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- The source-compressed root norm is an ambient matrix coefficient against
the same source vector; this is the coefficient form used by the direct
kernel route rather than an ambient HS assertion. -/
theorem sourceCompressedRoot_normSq_eq_ambient_inner
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (u : sourceSoninCarrier lambda) :
    ‖sourceCompressedRoot owner lambda u‖ ^ 2 =
      Complex.re (inner ℂ (sourceCompressedRoot owner lambda u)
        (sourceCompressedRoot owner lambda u)) := by
  exact (inner_self_eq_norm_sq (𝕜 := ℂ)
    (sourceCompressedRoot owner lambda u)).symm

/-- Exact four-term expansion of the source-compressed root.  Here `A = E Q E`
is the Hardy-compressed ambient corner and `R` is the committed prolate
remainder.  Thus the only term not containing the already controlled prolate
factor is the central source-kernel `J† A C A J`. -/
theorem sourceCompressedRoot_eq_hardyCorner_add_prolate_terms
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    sourceCompressedRoot owner lambda =
      (sourceInclusion lambda).adjoint ∘L
          (radialSupportProjection lambda ∘L
            sourceFourierSupportProjection lambda ∘L
            radialSupportProjection lambda) ∘L
          rootConvolution owner ∘L
          (radialSupportProjection lambda ∘L
            sourceFourierSupportProjection lambda ∘L
            radialSupportProjection lambda) ∘L
          sourceInclusion lambda -
        (sourceInclusion lambda).adjoint ∘L
          (radialSupportProjection lambda ∘L
            sourceFourierSupportProjection lambda ∘L
            radialSupportProjection lambda) ∘L
          rootConvolution owner ∘L sourceProlateRemainder lambda ∘L
          sourceInclusion lambda -
        (sourceInclusion lambda).adjoint ∘L sourceProlateRemainder lambda ∘L
          rootConvolution owner ∘L
          (radialSupportProjection lambda ∘L
            sourceFourierSupportProjection lambda ∘L
            radialSupportProjection lambda) ∘L
          sourceInclusion lambda +
        (sourceInclusion lambda).adjoint ∘L sourceProlateRemainder lambda ∘L
          rootConvolution owner ∘L sourceProlateRemainder lambda ∘L
          sourceInclusion lambda := by
  let J := sourceInclusion lambda
  let P := sourceSoninProjection lambda
  let A := radialSupportProjection lambda ∘L
    sourceFourierSupportProjection lambda ∘L radialSupportProjection lambda
  let R := sourceProlateRemainder lambda
  have hleft : J.adjoint ∘L P = J.adjoint := by
    simpa only [J] using sourceInclusionAdjoint_comp_sourceProjection lambda
  have hright : P ∘L J = J := by
    simpa only [J] using sourceSoninProjection_comp_sourceInclusion_eq_self lambda
  have hP : P = A - R := by
    simpa only [P, A, R] using
      sourceSoninProjection_eq_compression_sub_prolate lambda
  have hbase : sourceCompressedRoot owner lambda =
      J.adjoint ∘L P ∘L rootConvolution owner ∘L P ∘L J := by
    calc
      J.adjoint ∘L rootConvolution owner ∘L J =
          J.adjoint ∘L rootConvolution owner ∘L (P ∘L J) := by
        rw [hright]
      _ = (J.adjoint ∘L P) ∘L rootConvolution owner ∘L
          (P ∘L J) := by rw [hleft]
  rw [hbase, hP]
  apply ContinuousLinearMap.ext
  intro u
  simp [ContinuousLinearMap.comp_apply]
  dsimp [A, R]
  dsimp [J]
  abel_nf

/-! The one-sided form is the useful energy reduction: the source inclusion
already lands in the Sonin projection, so no second Hardy corner is needed. -/
theorem sourceCompressedRoot_eq_hardyCorner_sub_prolate_term
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    sourceCompressedRoot owner lambda =
      (sourceInclusion lambda).adjoint ∘L
          (radialSupportProjection lambda ∘L
            sourceFourierSupportProjection lambda ∘L
            radialSupportProjection lambda) ∘L
          rootConvolution owner ∘L sourceInclusion lambda -
        (sourceInclusion lambda).adjoint ∘L sourceProlateRemainder lambda ∘L
          rootConvolution owner ∘L sourceInclusion lambda := by
  let J := sourceInclusion lambda
  let P := sourceSoninProjection lambda
  let A := radialSupportProjection lambda ∘L
    sourceFourierSupportProjection lambda ∘L radialSupportProjection lambda
  let R := sourceProlateRemainder lambda
  have hleft : J.adjoint ∘L P = J.adjoint := by
    simpa only [J] using sourceInclusionAdjoint_comp_sourceProjection lambda
  have hP : P = A - R := by
    simpa only [P, A, R] using
      sourceSoninProjection_eq_compression_sub_prolate lambda
  have hbase : sourceCompressedRoot owner lambda =
      J.adjoint ∘L P ∘L rootConvolution owner ∘L J := by
    have hleft_apply (x : Carrier) : J.adjoint (P x) = J.adjoint x :=
      congrArg (fun f => f x) hleft
    apply ContinuousLinearMap.ext
    intro u
    change J.adjoint (rootConvolution owner (J u)) =
      J.adjoint (P (rootConvolution owner (J u)))
    exact (hleft_apply _).symm
  rw [hbase, hP]
  apply ContinuousLinearMap.ext
  intro u
  simp [ContinuousLinearMap.comp_apply, J, A, R]

end Dev
end ConnesWeilRH
