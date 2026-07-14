/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite conditioning space for a compact remainder

A compact operator sends the unit ball into a totally bounded set. A finite
`c`-net of that image spans a finite-dimensional subspace. On its orthogonal
complement the real quadratic form of the operator is bounded by `c`.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace CompactBadSpace

open Metric
open scoped InnerProductSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A compact operator cannot equal a nonzero scalar multiple of the identity
on an infinite-dimensional space. This is the compactness guard used to reject
an identically vanishing `-2 Id + K` remainder on the zero-integral subspace. -/
theorem not_compact_eq_smul_id
    (operator : H → H) (hcompact : IsCompactOperator operator)
    (scalar : ℂ) (hscalar : scalar ≠ 0)
    (hinfinite : ¬ FiniteDimensional ℂ H) :
    operator ≠ scalar • (id : H → H) := by
  intro heq
  have hscaled : IsCompactOperator ((scalar⁻¹ : ℂ) • operator) :=
    hcompact.smul (scalar⁻¹ : ℂ)
  rw [heq, smul_smul, inv_mul_cancel₀ hscalar, one_smul] at hscaled
  exact hinfinite (FiniteDimensional.of_isCompactOperator_id hscaled)

/-- A compact remainder has only finitely many conditioning directions above
any positive quadratic threshold. -/
theorem exists_finiteDimensional_controlSpace
    (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlSpace : Submodule ℂ H,
      FiniteDimensional ℂ controlSpace ∧
        ∀ x : H, x ∈ controlSpaceᗮ →
          (⟪x, operator x⟫_ℂ).re ≤ threshold * ‖x‖ ^ 2 := by
  obtain ⟨compactRange, hcompactRange, himage⟩ :=
    hcompact.image_closedBall_subset_compact 1
  obtain ⟨net, _hnet_subset, hnet_finite, hnet_cover⟩ :=
    hcompactRange.finite_cover_balls hthreshold
  let controlSpace : Submodule ℂ H := Submodule.span ℂ net
  have hfinite : FiniteDimensional ℂ controlSpace :=
    FiniteDimensional.span_of_finite ℂ hnet_finite
  refine ⟨controlSpace, hfinite, ?_⟩
  intro x hx
  by_cases hxzero : x = 0
  · simp [hxzero]
  let scale : ℝ := ‖x‖
  have hscale : scale ≠ 0 := by
    simpa [scale] using norm_ne_zero_iff.mpr hxzero
  let unit : H := (scale⁻¹ : ℂ) • x
  have hunit_norm : ‖unit‖ = 1 := by
    simp [unit, norm_smul, scale, hscale]
  have hunit_ball : unit ∈ closedBall (0 : H) 1 := by
    simp [mem_closedBall, hunit_norm]
  have hoperator_mem : operator unit ∈ compactRange :=
    himage ⟨unit, hunit_ball, rfl⟩
  have hcovered := hnet_cover hoperator_mem
  simp only [Set.mem_iUnion] at hcovered
  obtain ⟨center, hcenter_mem, hcenter_close⟩ := hcovered
  have hcenter_control : center ∈ controlSpace :=
    Submodule.subset_span hcenter_mem
  have hunit_orthogonal : unit ∈ controlSpaceᗮ := by
    exact (controlSpaceᗮ).smul_mem (scale⁻¹ : ℂ) hx
  have hinner_center : ⟪unit, center⟫_ℂ = 0 :=
    controlSpace.inner_left_of_mem_orthogonal hcenter_control hunit_orthogonal
  have hunit_bound : (⟪unit, operator unit⟫_ℂ).re ≤ threshold := by
    calc
      (⟪unit, operator unit⟫_ℂ).re =
          (⟪unit, operator unit - center⟫_ℂ).re := by
        rw [inner_sub_right, hinner_center, sub_zero]
      _ ≤ ‖⟪unit, operator unit - center⟫_ℂ‖ := by
        simpa only [RCLike.re_eq_complex_re] using
          RCLike.re_le_norm ⟪unit, operator unit - center⟫_ℂ
      _ ≤ ‖unit‖ * ‖operator unit - center‖ := norm_inner_le_norm _ _
      _ = ‖operator unit - center‖ := by rw [hunit_norm, one_mul]
      _ = dist (operator unit) center := by rw [dist_eq_norm]
      _ ≤ threshold := hcenter_close.le
  have hx_eq : x = (scale : ℂ) • unit := by
    simp [unit, smul_smul, hscale]
  have hinner_scale :
      (⟪x, operator x⟫_ℂ).re =
        scale ^ 2 * (⟪unit, operator unit⟫_ℂ).re := by
    rw [hx_eq, map_smul, inner_smul_left, inner_smul_right]
    simp [Complex.mul_re]
    ring
  rw [hinner_scale]
  simpa [scale, mul_comm] using
    mul_le_mul_of_nonneg_left hunit_bound (sq_nonneg scale)

/-- A compact remainder admits a finite control frame made of actual values of
an arbitrary dense source family.  The frame is the finite-dimensional
replacement for an arbitrary compact-net basis: every chosen direction is a
source value, so later interpolation/evaluation constraints can refer to the
same source objects. -/
theorem exists_finite_source_controlFrame
    {ι : Type*} (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    (source : ι → H) (hdense : DenseRange source)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ sourceFrame : Set H,
      sourceFrame.Finite ∧
        sourceFrame ⊆ Set.range source ∧
          FiniteDimensional ℂ (Submodule.span ℂ sourceFrame) ∧
            ∀ x : H, x ∈ (Submodule.span ℂ sourceFrame)ᗮ →
              (⟪x, operator x⟫_ℂ).re ≤ threshold * ‖x‖ ^ 2 := by
  let half : ℝ := threshold / 2
  have hhalf : 0 < half := by
    dsimp [half]
    linarith
  obtain ⟨compactRange, hcompactRange, himage⟩ :=
    hcompact.image_closedBall_subset_compact 1
  obtain ⟨net, _hnet_subset, hnet_finite, hnet_cover⟩ :=
    hcompactRange.finite_cover_balls hhalf
  let chooseIndex : H → ι := fun center =>
    Classical.choose (hdense.exists_dist_lt center hhalf)
  have chooseIndex_spec (center : H) :
      dist center (source (chooseIndex center)) < half := by
    dsimp [chooseIndex]
    exact Classical.choose_spec (hdense.exists_dist_lt center hhalf)
  let sourceFrame : Set H :=
    (fun center => source (chooseIndex center)) '' net
  have hsourceFrame_finite : sourceFrame.Finite := by
    dsimp [sourceFrame]
    exact hnet_finite.image _
  have hsourceFrame_range : sourceFrame ⊆ Set.range source := by
    rintro y ⟨center, _hcenter, rfl⟩
    exact ⟨chooseIndex center, rfl⟩
  have hfinite : FiniteDimensional ℂ (Submodule.span ℂ sourceFrame) :=
    FiniteDimensional.span_of_finite ℂ hsourceFrame_finite
  refine ⟨sourceFrame, hsourceFrame_finite, hsourceFrame_range, hfinite, ?_⟩
  intro x hx
  by_cases hxzero : x = 0
  · simp [hxzero]
  let scale : ℝ := ‖x‖
  have hscale : scale ≠ 0 := by
    simpa [scale] using norm_ne_zero_iff.mpr hxzero
  let unit : H := (scale⁻¹ : ℂ) • x
  have hunit_norm : ‖unit‖ = 1 := by
    simp [unit, norm_smul, scale, hscale]
  have hunit_ball : unit ∈ closedBall (0 : H) 1 := by
    simp [mem_closedBall, hunit_norm]
  have hoperator_mem : operator unit ∈ compactRange :=
    himage ⟨unit, hunit_ball, rfl⟩
  have hcovered := hnet_cover hoperator_mem
  simp only [Set.mem_iUnion] at hcovered
  obtain ⟨center, hcenter_mem, hcenter_close⟩ := hcovered
  let sourcePoint : H := source (chooseIndex center)
  have hsource_close : dist center sourcePoint < half := by
    exact chooseIndex_spec center
  have hsource_control : sourcePoint ∈ Submodule.span ℂ sourceFrame := by
    apply Submodule.subset_span
    exact ⟨center, hcenter_mem, rfl⟩
  have hunit_orthogonal : unit ∈ (Submodule.span ℂ sourceFrame)ᗮ := by
    exact ((Submodule.span ℂ sourceFrame)ᗮ).smul_mem
      (scale⁻¹ : ℂ) hx
  have hinner_source : ⟪unit, sourcePoint⟫_ℂ = 0 :=
    (Submodule.span ℂ sourceFrame).inner_left_of_mem_orthogonal
      hsource_control hunit_orthogonal
  have hunit_bound : (⟪unit, operator unit⟫_ℂ).re ≤ threshold := by
    calc
      (⟪unit, operator unit⟫_ℂ).re =
          (⟪unit, operator unit - sourcePoint⟫_ℂ).re := by
        rw [inner_sub_right, hinner_source, sub_zero]
      _ ≤ ‖⟪unit, operator unit - sourcePoint⟫_ℂ‖ := by
        simpa only [RCLike.re_eq_complex_re] using
          RCLike.re_le_norm ⟪unit, operator unit - sourcePoint⟫_ℂ
      _ ≤ ‖unit‖ * ‖operator unit - sourcePoint‖ := norm_inner_le_norm _ _
      _ = ‖operator unit - sourcePoint‖ := by rw [hunit_norm, one_mul]
      _ = dist (operator unit) sourcePoint := by rw [dist_eq_norm]
      _ ≤ dist (operator unit) center + dist center sourcePoint :=
        dist_triangle _ _ _
      _ ≤ half + half := (add_lt_add hcenter_close hsource_close).le
      _ = threshold := by dsimp [half]; ring
  have hx_eq : x = (scale : ℂ) • unit := by
    simp [unit, smul_smul, hscale]
  have hinner_scale :
      (⟪x, operator x⟫_ℂ).re =
        scale ^ 2 * (⟪unit, operator unit⟫_ℂ).re := by
    rw [hx_eq, map_smul, inner_smul_left, inner_smul_right]
    simp [Complex.mul_re]
    ring
  rw [hinner_scale]
  simpa [scale, mul_comm] using
    mul_le_mul_of_nonneg_left hunit_bound (sq_nonneg scale)

/-- A finite detector row family can consume the source frame exactly once its
span contains that frame.  The row equations are stated as inner products, so
the theorem exposes the precise remaining producer obligation: prove the
finite row span covers the compact-remainder frame. -/
theorem exists_finite_source_controlFrame_with_finite_row_vanishing
    {ι : Type*} (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    (source : ι → H) (hdense : DenseRange source)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ sourceFrame : Set H,
      sourceFrame.Finite ∧
        sourceFrame ⊆ Set.range source ∧
          FiniteDimensional ℂ (Submodule.span ℂ sourceFrame) ∧
            ∀ (n : ℕ) (rows : Fin n → H),
              Submodule.span ℂ sourceFrame ≤
                  Submodule.span ℂ (Set.range rows) →
                ∀ x : H,
                  (∀ i : Fin n, ⟪x, rows i⟫_ℂ = 0) →
                    (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  obtain ⟨sourceFrame, hfiniteFrame, hframeRange, hfinite, hbound⟩ :=
    exists_finite_source_controlFrame operator hcompact source hdense hthreshold
  refine ⟨sourceFrame, hfiniteFrame, hframeRange, hfinite, ?_⟩
  intro n rows hcoverage x hrows
  have hxRows : x ∈ (Submodule.span ℂ (Set.range rows))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro y hy
      obtain ⟨i, rfl⟩ := hy
      exact hrows i
    · simp
    · intro y z hy hz hiy hiz
      rw [inner_add_right, hiy, hiz, add_zero]
    · intro a y hy hiy
      rw [inner_smul_right, hiy, mul_zero]
  have hxControl : x ∈ (Submodule.span ℂ sourceFrame)ᗮ :=
    Submodule.orthogonal_le hcoverage hxRows
  have h := hbound x hxControl
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.sub_re, Complex.mul_re]
  norm_num
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  linarith

/-- If the algebraic span of a row family is dense, compactness selects a
finite set of actual row values whose vanishing controls the shifted quadratic
form.  Unlike `DenseRange rows`, density is required only after taking the
linear span, which is the natural completeness condition for Mellin/Fourier
families. -/
theorem exists_finite_controlRows_of_dense_span
    {ι : Type*} (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    (rows : ι → H)
    (hdense : Dense (Submodule.span ℂ (Set.range rows) : Set H))
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlRows : Finset H,
      (controlRows : Set H) ⊆ Set.range rows ∧
        FiniteDimensional ℂ (Submodule.span ℂ (controlRows : Set H)) ∧
          ∀ x : H,
            (∀ row ∈ controlRows, ⟪x, row⟫_ℂ = 0) →
              (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  let rowSpan : Submodule ℂ H := Submodule.span ℂ (Set.range rows)
  have hdenseRange : DenseRange ((↑) : rowSpan → H) :=
    hdense.denseRange_val
  obtain ⟨sourceFrame, hframeFinite, hframeRange, _hframeFD, hbound⟩ :=
    exists_finite_source_controlFrame operator hcompact
      ((↑) : rowSpan → H) hdenseRange hthreshold
  have hframeRowSpan : sourceFrame ⊆ (rowSpan : Set H) := by
    intro y hy
    rcases hframeRange hy with ⟨z, rfl⟩
    exact z.property
  let frameFinset : Finset H := hframeFinite.toFinset
  have hframeFinsetSpan : (frameFinset : Set H) ⊆ rowSpan := by
    intro y hy
    apply hframeRowSpan
    exact (Set.Finite.mem_toFinset hframeFinite).mp hy
  obtain ⟨controlRows, hcontrolRowsRange, hframeControl⟩ :=
    Submodule.subset_span_finite_of_subset_span
      (s := Set.range rows) (t := frameFinset) (by
        simpa [rowSpan] using hframeFinsetSpan)
  refine ⟨controlRows, hcontrolRowsRange,
    FiniteDimensional.span_of_finite ℂ controlRows.finite_toSet, ?_⟩
  intro x hrows
  have hxControlRows :
      x ∈ (Submodule.span ℂ (controlRows : Set H))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro y hy
      exact hrows y (by simpa using hy)
    · simp
    · intro y z hy hz hiy hiz
      rw [inner_add_right, hiy, hiz, add_zero]
    · intro a y hy hiy
      rw [inner_smul_right, hiy, mul_zero]
  have hspanFrame :
      Submodule.span ℂ sourceFrame ≤
        Submodule.span ℂ (controlRows : Set H) := by
    apply Submodule.span_le.2
    intro y hy
    apply hframeControl
    exact (Set.Finite.mem_toFinset hframeFinite).2 hy
  have hxFrame : x ∈ (Submodule.span ℂ sourceFrame)ᗮ :=
    Submodule.orthogonal_le hspanFrame hxControlRows
  have h := hbound x hxFrame
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.sub_re, Complex.mul_re]
  norm_num
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  linarith

/-- Indexed form of `exists_finite_controlRows_of_dense_span`.  The selected
finite constraints retain their original row indices, so a downstream owner
can interpret them as frequencies, Mellin nodes, or detector labels. -/
theorem exists_finite_controlRowIndices_of_dense_span
    {ι : Type*} (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    (rows : ι → H)
    (hdense : Dense (Submodule.span ℂ (Set.range rows) : Set H))
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ rowIndices : Finset ι,
      FiniteDimensional ℂ
          (Submodule.span ℂ (rows '' (rowIndices : Set ι))) ∧
        ∀ x : H,
          (∀ i ∈ rowIndices, ⟪x, rows i⟫_ℂ = 0) →
            (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  classical
  obtain ⟨controlRows, hcontrolRange, _hfinite, hsign⟩ :=
    exists_finite_controlRows_of_dense_span
      operator hcompact rows hdense hthreshold
  let chooseIndex : {row // row ∈ controlRows} → ι := fun row =>
    Classical.choose (hcontrolRange row.property)
  have chooseIndex_spec (row : {row // row ∈ controlRows}) :
      rows (chooseIndex row) = row.1 := by
    exact Classical.choose_spec (hcontrolRange row.property)
  let rowIndices : Finset ι := controlRows.attach.image chooseIndex
  have hfiniteSpan : FiniteDimensional ℂ
      (Submodule.span ℂ (rows '' (rowIndices : Set ι))) :=
    FiniteDimensional.span_of_finite ℂ
      (rowIndices.finite_toSet.image rows)
  refine ⟨rowIndices, hfiniteSpan, ?_⟩
  intro x hrows
  apply hsign x
  intro row hrow
  let row' : {row // row ∈ controlRows} := ⟨row, hrow⟩
  have hrow'_attach : row' ∈ controlRows.attach := by
    simp [row']
  have hi : chooseIndex row' ∈ rowIndices := by
    apply Finset.mem_image.2
    exact ⟨row', hrow'_attach, rfl⟩
  have hz := hrows (chooseIndex row') hi
  rw [chooseIndex_spec row'] at hz
  exact hz

/-- Every Hilbert basis is a complete row family, so a compact remainder is
nonpositive after imposing only finitely many basis-coordinate equations. -/
theorem exists_finite_hilbertBasis_controlRowIndices
    {ι : Type*} (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    (basis : HilbertBasis ι ℂ H)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ rowIndices : Finset ι,
      FiniteDimensional ℂ
          (Submodule.span ℂ (basis '' (rowIndices : Set ι))) ∧
        ∀ x : H,
          (∀ i ∈ rowIndices, ⟪x, basis i⟫_ℂ = 0) →
            (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  apply exists_finite_controlRowIndices_of_dense_span
    operator hcompact basis
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr basis.dense_span
  · exact hthreshold

/-- The source-frame theorem in the control-space shape used by downstream
consumers. -/
theorem exists_finiteDimensional_controlSpace_spanned_by_denseRange
    {ι : Type*} (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    (source : ι → H) (hdense : DenseRange source)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlSpace : Submodule ℂ H,
      FiniteDimensional ℂ controlSpace ∧
        controlSpace ≤ Submodule.span ℂ (Set.range source) ∧
          ∀ x : H, x ∈ controlSpaceᗮ →
            (⟪x, operator x⟫_ℂ).re ≤ threshold * ‖x‖ ^ 2 := by
  obtain ⟨sourceFrame, _hfiniteFrame, hframe_range, hfinite, hbound⟩ :=
    exists_finite_source_controlFrame operator hcompact source hdense hthreshold
  let controlSpace : Submodule ℂ H := Submodule.span ℂ sourceFrame
  have hcontrol_finite : FiniteDimensional ℂ controlSpace := by
    simpa [controlSpace] using hfinite
  have hcontrol_le : controlSpace ≤ Submodule.span ℂ (Set.range source) := by
    dsimp [controlSpace]
    exact Submodule.span_mono hframe_range
  exact ⟨controlSpace, hcontrol_finite, hcontrol_le, by simpa [controlSpace] using hbound⟩

/-- The source-frame control theorem after shifting the quadratic form by the
positive threshold. -/
theorem exists_finiteDimensional_remainder_nonpositive_spanned_by_denseRange
    {ι : Type*} (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    (source : ι → H) (hdense : DenseRange source)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlSpace : Submodule ℂ H,
      FiniteDimensional ℂ controlSpace ∧
        controlSpace ≤ Submodule.span ℂ (Set.range source) ∧
          ∀ x : H, x ∈ controlSpaceᗮ →
            (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  obtain ⟨controlSpace, hfinite, hcontrol, hbound⟩ :=
    exists_finiteDimensional_controlSpace_spanned_by_denseRange
      operator hcompact source hdense hthreshold
  refine ⟨controlSpace, hfinite, hcontrol, ?_⟩
  intro x hx
  have h := hbound x hx
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.sub_re, Complex.mul_re]
  norm_num
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  linarith

/-- On the orthogonal complement of the finite control space, the compact
perturbation of `-threshold * Id` has nonpositive real quadratic form. -/
theorem exists_finiteDimensional_remainder_nonpositive
    (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlSpace : Submodule ℂ H,
      FiniteDimensional ℂ controlSpace ∧
        ∀ x : H, x ∈ controlSpaceᗮ →
          (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  obtain ⟨controlSpace, hfinite, hbound⟩ :=
    exists_finiteDimensional_controlSpace operator hcompact hthreshold
  refine ⟨controlSpace, hfinite, ?_⟩
  intro x hx
  have h := hbound x hx
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.sub_re, Complex.mul_re]
  norm_num
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  linarith

/-- If an evaluation space contains every compact-remainder control direction,
then vectors satisfying all of its vanishing conditions lie in the control
space orthogonal complement. -/
theorem mem_controlSpace_orthogonal_of_le_evaluationSpace
    {controlSpace evaluationSpace : Submodule ℂ H}
    (hcontrol : controlSpace ≤ evaluationSpace)
    {x : H} (hx : x ∈ evaluationSpaceᗮ) :
    x ∈ controlSpaceᗮ :=
  Submodule.orthogonal_le hcontrol hx

/-- A compact remainder is nonpositive on the vanishing space of every
evaluation space that contains the finite-dimensional control space. This is
the abstract consumer for the route's finite bad-space containment gate. -/
theorem exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace
    (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlSpace : Submodule ℂ H,
      FiniteDimensional ℂ controlSpace ∧
        ∀ evaluationSpace : Submodule ℂ H,
          controlSpace ≤ evaluationSpace →
            ∀ x : H, x ∈ evaluationSpaceᗮ →
              (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  obtain ⟨controlSpace, hfinite, hnonpositive⟩ :=
    exists_finiteDimensional_remainder_nonpositive operator hcompact hthreshold
  refine ⟨controlSpace, hfinite, ?_⟩
  intro evaluationSpace hcontrol x hx
  exact hnonpositive x
    (mem_controlSpace_orthogonal_of_le_evaluationSpace hcontrol hx)

/-- The evaluation-space consumer with a source-span containment witness. -/
theorem exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace_spanned_by_denseRange
    {ι : Type*} (operator : H →L[ℂ] H) (hcompact : IsCompactOperator operator)
    (source : ι → H) (hdense : DenseRange source)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ controlSpace : Submodule ℂ H,
      FiniteDimensional ℂ controlSpace ∧
        controlSpace ≤ Submodule.span ℂ (Set.range source) ∧
          ∀ evaluationSpace : Submodule ℂ H,
            controlSpace ≤ evaluationSpace →
              ∀ x : H, x ∈ evaluationSpaceᗮ →
                (⟪x, operator x - (threshold : ℂ) • x⟫_ℂ).re ≤ 0 := by
  obtain ⟨controlSpace, hfinite, hcontrol, hnonpositive⟩ :=
    exists_finiteDimensional_remainder_nonpositive_spanned_by_denseRange
      operator hcompact source hdense hthreshold
  refine ⟨controlSpace, hfinite, hcontrol, ?_⟩
  intro evaluationSpace hcontrolEval x hx
  exact hnonpositive x
    (mem_controlSpace_orthogonal_of_le_evaluationSpace hcontrolEval hx)

end CompactBadSpace
end CC20Concrete
end Source
end ConnesWeilRH
