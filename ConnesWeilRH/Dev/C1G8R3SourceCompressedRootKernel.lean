/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3GateAmbientNormalForm

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

end Dev
end ConnesWeilRH
