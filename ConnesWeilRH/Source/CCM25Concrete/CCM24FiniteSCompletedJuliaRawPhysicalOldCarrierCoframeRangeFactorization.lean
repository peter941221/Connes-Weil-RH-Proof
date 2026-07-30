/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer

/-!
# Range factorization for the old-carrier coframe channel

This module isolates the exact algebra needed before a source-specific
coframe readout can be constructed.  If `N` is an isometric frame, then
`Q = I - N N†` is the orthogonal complement of its range.  If `V` is a
right inverse of `U` and a row `B` kills `V† (range N)`, the row factors
through the physical boundary channel `Q U†`:

```text
F = B V† Q
F Q U† = B.
```

The annihilation condition is deliberately an explicit premise.  It is the
source theorem still required by Bone 1; it is not inferred from boundedness
or from the frame isometry alone.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeFactorization

open scoped InnerProduct InnerProductSpace

/-! ## Exact factor -/

noncomputable def rangeFactor
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (row : K →L[ℂ] G) (inverse : K →L[ℂ] K)
    (frame : H →L[ℂ] K) : K →L[ℂ] G :=
  row ∘L ContinuousLinearMap.adjoint inverse ∘L
    (ContinuousLinearMap.id ℂ K - frame ∘L
      ContinuousLinearMap.adjoint frame)

theorem rangeFactor_comp_complement_comp_transportAdjoint_eq
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (row : K →L[ℂ] G) (transport inverse : K →L[ℂ] K)
    (frame : H →L[ℂ] K)
    (hframe : ContinuousLinearMap.adjoint frame ∘L frame =
      ContinuousLinearMap.id ℂ H)
    (htransport : transport ∘L inverse =
      ContinuousLinearMap.id ℂ K)
    (hannihilate : row ∘L ContinuousLinearMap.adjoint inverse ∘L frame = 0) :
    rangeFactor row inverse frame ∘L
        (ContinuousLinearMap.id ℂ K - frame ∘L
          ContinuousLinearMap.adjoint frame) ∘L
        ContinuousLinearMap.adjoint transport = row := by
  have hprojection_sq :
      (ContinuousLinearMap.id ℂ K - frame ∘L
          ContinuousLinearMap.adjoint frame) ∘L
        (ContinuousLinearMap.id ℂ K - frame ∘L
          ContinuousLinearMap.adjoint frame) =
        (ContinuousLinearMap.id ℂ K - frame ∘L
          ContinuousLinearMap.adjoint frame) := by
    apply ContinuousLinearMap.ext
    intro x
    have hframe_point := congrArg
      (fun operator : H →L[ℂ] H =>
        frame (operator (ContinuousLinearMap.adjoint frame x))) hframe
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hframe_point
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      map_sub]
    rw [hframe_point]
    abel
  have hadjoint_transport :
      ContinuousLinearMap.adjoint inverse ∘L
          ContinuousLinearMap.adjoint transport =
        ContinuousLinearMap.id ℂ K := by
    have h := congrArg ContinuousLinearMap.adjoint htransport
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id] using h
  calc
    rangeFactor row inverse frame ∘L
          (ContinuousLinearMap.id ℂ K - frame ∘L
            ContinuousLinearMap.adjoint frame) ∘L
          ContinuousLinearMap.adjoint transport =
        row ∘L ContinuousLinearMap.adjoint inverse ∘L
          (ContinuousLinearMap.id ℂ K - frame ∘L
            ContinuousLinearMap.adjoint frame) ∘L
          (ContinuousLinearMap.id ℂ K - frame ∘L
            ContinuousLinearMap.adjoint frame) ∘L
          ContinuousLinearMap.adjoint transport := by
      rfl
    _ = row ∘L ContinuousLinearMap.adjoint inverse ∘L
          (ContinuousLinearMap.id ℂ K - frame ∘L
            ContinuousLinearMap.adjoint frame) ∘L
          ContinuousLinearMap.adjoint transport := by
      apply ContinuousLinearMap.ext
      intro x
      have hpoint := congrArg
        (fun operator : K →L[ℂ] K =>
          operator (ContinuousLinearMap.adjoint transport x)) hprojection_sq
      simp only [ContinuousLinearMap.comp_apply] at hpoint
      simpa only [ContinuousLinearMap.comp_apply] using
        congrArg
          (fun z : K =>
            row (ContinuousLinearMap.adjoint inverse z)) hpoint
    _ = row ∘L ContinuousLinearMap.adjoint inverse ∘L
          ContinuousLinearMap.adjoint transport -
          (row ∘L ContinuousLinearMap.adjoint inverse ∘L frame) ∘L
            ContinuousLinearMap.adjoint frame ∘L
              ContinuousLinearMap.adjoint transport := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        map_sub]
    _ = row ∘L ContinuousLinearMap.adjoint inverse ∘L
          ContinuousLinearMap.adjoint transport := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply]
      have hpoint := congrArg
        (fun operator : H →L[ℂ] G =>
          operator (ContinuousLinearMap.adjoint frame
            (ContinuousLinearMap.adjoint transport x))) hannihilate
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply] at hpoint
      rw [hpoint]
      simp
    _ = row := by
      rw [hadjoint_transport, ContinuousLinearMap.comp_id]

/-! ## Norm bookkeeping -/

theorem rangeFactor_norm_le
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (row : K →L[ℂ] G) (inverse : K →L[ℂ] K)
    (frame : H →L[ℂ] K)
    (rowBound inverseBound : ℝ)
    (hframe : ContinuousLinearMap.adjoint frame ∘L frame =
      ContinuousLinearMap.id ℂ H)
    (hrow : ‖row‖ ≤ rowBound) (hinverse : ‖inverse‖ ≤ inverseBound)
    (hrow_nonneg : 0 ≤ rowBound) (hinverse_nonneg : 0 ≤ inverseBound) :
    ‖rangeFactor row inverse frame‖ ≤ rowBound * inverseBound := by
  have hprojection :
      ‖ContinuousLinearMap.id ℂ K - frame ∘L
          ContinuousLinearMap.adjoint frame‖ ≤ (1 : ℝ) := by
    let projection : K →L[ℂ] K :=
      frame ∘L ContinuousLinearMap.adjoint frame
    have hprojection_adj : projection† = projection := by
      simp only [projection, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint]
    have hprojection_sq : projection ∘L projection = projection := by
      apply ContinuousLinearMap.ext
      intro x
      have hframe_point := congrArg
        (fun operator : H →L[ℂ] H =>
          frame (operator (ContinuousLinearMap.adjoint frame x))) hframe
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] at hframe_point
      simpa only [projection, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using hframe_point
    have hprojection_star : IsStarProjection projection := by
      refine
        { isIdempotentElem := ?_
          isSelfAdjoint := ?_ }
      · simpa only [ContinuousLinearMap.mul_def] using hprojection_sq
      · change projection† = projection
        exact hprojection_adj
    have hcomplement : IsStarProjection
        (ContinuousLinearMap.id ℂ K - projection) :=
      hprojection_star.one_sub
    simpa only [projection] using IsStarProjection.norm_le _ hcomplement
  have hrow_nonneg' : 0 ≤ ‖row‖ := norm_nonneg row
  have hinverse_adj : ‖ContinuousLinearMap.adjoint inverse‖ ≤ inverseBound := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hinverse
  unfold rangeFactor
  calc
    ‖(row ∘L ContinuousLinearMap.adjoint inverse) ∘L
        (ContinuousLinearMap.id ℂ K - frame ∘L
          ContinuousLinearMap.adjoint frame)‖ ≤
        ‖row‖ *
          ‖ContinuousLinearMap.adjoint inverse‖ *
            ‖ContinuousLinearMap.id ℂ K - frame ∘L
              ContinuousLinearMap.adjoint frame‖ := by
      calc
        ‖(row ∘L ContinuousLinearMap.adjoint inverse) ∘L
            (ContinuousLinearMap.id ℂ K - frame ∘L
              ContinuousLinearMap.adjoint frame)‖ ≤
            ‖row ∘L ContinuousLinearMap.adjoint inverse‖ *
              ‖ContinuousLinearMap.id ℂ K - frame ∘L
                ContinuousLinearMap.adjoint frame‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖row‖ * ‖ContinuousLinearMap.adjoint inverse‖) *
              ‖ContinuousLinearMap.id ℂ K - frame ∘L
                ContinuousLinearMap.adjoint frame‖ := by
          exact mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _)
        _ = ‖row‖ * ‖ContinuousLinearMap.adjoint inverse‖ *
              ‖ContinuousLinearMap.id ℂ K - frame ∘L
                ContinuousLinearMap.adjoint frame‖ := by ring
    _ ≤ rowBound * inverseBound * 1 := by
      exact mul_le_mul
        (mul_le_mul hrow hinverse_adj (norm_nonneg _) hrow_nonneg)
        hprojection (norm_nonneg _) (mul_nonneg hrow_nonneg hinverse_nonneg)
    _ = rowBound * inverseBound := by ring

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
