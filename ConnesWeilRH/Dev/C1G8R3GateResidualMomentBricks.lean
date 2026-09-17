/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24LogRadialSupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace

/-!
# Gate-residual moment bricks (wave V, record 1588)

Four bricks for the re-typed gate residual of records 1586--1587.  All of them
are stated on committed objects, and all of them are gap-free: every spectral,
density or trace input appears only as a HYPOTHESIS.

* `radialSupportProjection_fixes_of_support_subset` -- the pointwise form of
  the `hradial` brick: an a.e. support hypothesis `t < Real.log lambda - s`
  makes the wider radial projection fix the vector.  The absorption side is
  already committed (`wideRadial_absorption_of_sourceRadialSupport`,
  `C1G8R3CompositeBoundaryEnergy.lean:175`), which consumes precisely the
  membership this lemma produces.
* `norm_sq_sub_starProjection_eq_add` -- the exact Pythagorean split of the
  residual for NESTED projections: record 1587 section 2.1 in operator form.
* `norm_sq_sub_starProjection_le_of_quadraticFormGap` -- the first-moment to
  zeroth-moment conversion along a quadratic-form gap on the orthogonal
  complement of the fixed space.  This is the complement-restricted,
  basis-summable form of the conversion; the committed operator-norm adapter
  (`normSq_le_of_spectralGap_of_norm_le`) is a whole-space statement and
  cannot be summed over a basis.
* `starProjection_eq_self_of_re_inner_eq_normSq` -- the equality case used in
  record 1586 section 1 (`range(P) = ker(1 - EQE)`).

Mathlib already supplies the nested-projection COMPOSITION
(`Submodule.starProjection_comp_starProjection_of_le`); the concrete
corollaries below are the project-level instances of it, so no new copy of
that lemma is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGateResidualMomentBricks

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open MeasureTheory
open scoped InnerProductSpace

/-! ## 1. The concrete projection pair `P <= E` and `P <= Q` -/

/-- Every complete archimedean Sonin vector is radially supported: the Sonin
space is the infimum of the radial and the Fourier support conditions. -/
theorem sourceSoninProjection_le_radialSupportProjection
    (lambda : CCM24SoninScale) :
    (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule ≤
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule :=
  inf_le_left

/-- Every complete archimedean Sonin vector satisfies the Fourier support
condition. -/
theorem sourceSoninProjection_le_sourceFourierSupportProjection
    (lambda : CCM24SoninScale) :
    (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule ≤
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule :=
  inf_le_right

/-- The radial projection fixes the Sonin projection: `E P = P`.  This is the
project-level instance of `Submodule.starProjection_comp_starProjection_of_le`
in the order the wide-radial absorption lemmas consume it. -/
theorem radialSupportProjection_comp_sourceSoninProjection
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda ∘L sourceSoninProjection lambda =
      sourceSoninProjection lambda := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, radialSupportProjection,
    sourceSoninProjection]
  exact (Submodule.starProjection_eq_self_iff (K :=
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule)).mpr
    (sourceSoninProjection_le_radialSupportProjection lambda
      (Submodule.starProjection_apply_mem _ x))

/-- The Sonin projection absorbs the radial projection: `P E = P`. -/
theorem sourceSoninProjection_comp_radialSupportProjection
    (lambda : CCM24SoninScale) :
    sourceSoninProjection lambda ∘L radialSupportProjection lambda =
      sourceSoninProjection lambda :=
  Submodule.starProjection_comp_starProjection_of_le
    (sourceSoninProjection_le_radialSupportProjection lambda)

/-! ## 2. Transport `=>` wide radial support, in pointwise form -/

/-- A vector whose support starts at `Real.log lambda - s` (almost everywhere)
is fixed by the radial projection at any scale `lambda'` with
`Real.log lambda' = Real.log lambda - s`.

This is the honest pointwise residue of the `hradial` brick: `hwide` consumers
(`wideRadial_absorption_of_sourceRadialSupport`) take absorption at the narrow
scale as a hypothesis, and this lemma is what turns a support statement from
the transport ledger into that hypothesis at the wide scale.  The instance
`lambda' := wideRadialScale lambda s` with
`hlog := realLog_wideRadialScale lambda s` lives in
`C1G8R3CompositeBoundaryEnergy.lean:108-112`. -/
theorem radialSupportProjection_fixes_of_support_subset
    (lambda lambda' : CCM24SoninScale) (s : ℝ)
    (hlog : Real.log lambda' = Real.log lambda - s)
    (v : finiteSCarrier)
    (hv : ∀ᵐ t ∂(volume : Measure ℝ), t < Real.log lambda - s → v t = 0) :
    radialSupportProjection lambda' v = v := by
  have hmem : v ∈ ccm24LogRadialSupportClosedSubspace lambda' := by
    rw [mem_ccm24LogRadialSupportClosedSubspace_iff]
    filter_upwards [hv] with t ht
    intro hlt
    exact ht (hlog ▸ hlt)
  have h := (ccm24LogRadialSupportProjection_eq_self_iff lambda' v).2 hmem
  simpa only [radialSupportProjection, ccm24LogRadialSupportProjection] using h

/-! ## 3. The abstract bricks -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exact Pythagorean split of the residual for NESTED orthogonal
projections: record 1587 section 2.1.  The two summands on the right are
orthogonal, and no hypothesis beyond the inclusion is used. -/
theorem norm_sq_sub_starProjection_eq_add
    {W₁ W₂ : Submodule ℂ H} [W₁.HasOrthogonalProjection]
    [W₂.HasOrthogonalProjection] (hle : W₁ ≤ W₂) (x : H) :
    ‖x - W₁.starProjection x‖ ^ 2 =
      ‖x - W₂.starProjection x‖ ^ 2 +
        ‖W₂.starProjection x - W₁.starProjection x‖ ^ 2 := by
  have hmem : W₂.starProjection x - W₁.starProjection x ∈ W₂ :=
    Submodule.sub_mem W₂ (Submodule.starProjection_apply_mem W₂ x)
      (hle (Submodule.starProjection_apply_mem W₁ x))
  have horth : ⟪x - W₂.starProjection x,
      W₂.starProjection x - W₁.starProjection x⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero (K := W₂) x _ hmem
  have hsplit : x - W₁.starProjection x =
      (x - W₂.starProjection x) +
        (W₂.starProjection x - W₁.starProjection x) := by
    abel
  rw [hsplit]
  simp only [sq]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth

/-- The concrete instance of the nested split at the project's own pair
(`P = sourceSoninProjection <= E = radialSupportProjection`): the residual
column splits into the radial-escape mass and the carrier-distance mass. -/
theorem norm_sq_sub_sourceSoninProjection_eq_add
    (lambda : CCM24SoninScale) (x : finiteSCarrier) :
    ‖x - sourceSoninProjection lambda x‖ ^ 2 =
      ‖x - radialSupportProjection lambda x‖ ^ 2 +
        ‖radialSupportProjection lambda x -
          sourceSoninProjection lambda x‖ ^ 2 := by
  have h := norm_sq_sub_starProjection_eq_add
    (W₁ := (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule)
    (W₂ := (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule)
    (sourceSoninProjection_le_radialSupportProjection lambda) x
  simpa only [sourceSoninProjection, radialSupportProjection] using h

/-- Equality case for a projection: if the inner product of `h` with its own
projection already equals `‖h‖ ^ 2`, then the projection fixes `h`.

This is the step that identifies the carrier with the fixed space of the
compression in record 1586 section 1: there one has
`⟪h, Q h⟫ = ‖h‖ ^ 2` and `‖Q h‖ <= ‖h‖`, whence `Q h = h`. -/
theorem starProjection_eq_self_of_re_inner_eq_normSq
    {W : Submodule ℂ H} [W.HasOrthogonalProjection] {h : H} (hne : h ≠ 0)
    (hinner : (⟪h, W.starProjection h⟫_ℂ).re = ‖h‖ ^ 2) :
    W.starProjection h = h := by
  have hnorm : ‖h‖ ≤ ‖W.starProjection h‖ := by
    have hle : (inner ℂ h (W.starProjection h)).re ≤
        ‖h‖ * ‖W.starProjection h‖ :=
      re_inner_le_norm (𝕜 := ℂ) h (W.starProjection h)
    rw [hinner] at hle
    have hmul : ‖h‖ * ‖h‖ ≤ ‖h‖ * ‖W.starProjection h‖ := by
      simpa only [sq] using hle
    exact le_of_mul_le_mul_left hmul (norm_pos_iff.mpr hne)
  have hnorm' : ‖W.starProjection h‖ ≤ ‖h‖ :=
    Submodule.norm_starProjection_apply_le (K := W) h
  exact (Submodule.starProjection_eq_self_iff (K := W)).mpr
    ((Submodule.mem_iff_norm_starProjection W h).mpr
      (le_antisymm hnorm' hnorm))

/-- First moment to zeroth moment under a quadratic-form gap: if the
self-adjoint operator `K` has fixed space exactly `W` and its quadratic form
dominates `gap * ‖y‖ ^ 2` on the orthogonal complement of `W`, then the square
distance to `W` is bounded by `gap⁻¹` times the quadratic form of `1 - K` at
the same vector.

This is the per-vector form of record 1587 section 3.  Unlike the committed
operator-norm adapter it is stated on the complement alone, so it can be
summed over any orthonormal family: the resulting bound is a trace bound, not
a norm bound.  No gap is asserted here; `hform` is the hypothesis. -/
theorem norm_sq_sub_starProjection_le_of_quadraticFormGap
    {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (K : H →L[ℂ] H) {gap : ℝ} (hgap : 0 < gap)
    (hsym : ∀ u v : H, inner ℂ (K u) v = inner ℂ u (K v))
    (hfix : ∀ u : H, u ∈ W ↔ K u = u)
    (hform : ∀ y : H, (∀ w ∈ W, inner ℂ y w = 0) →
      gap * ‖y‖ ^ 2 ≤ (inner ℂ y (y - K y)).re)
    (x : H) :
    ‖x - W.starProjection x‖ ^ 2 ≤
      gap⁻¹ * (inner ℂ x (x - K x)).re := by
  have hPmem : W.starProjection x ∈ W := Submodule.starProjection_apply_mem W x
  have hKP : K (W.starProjection x) = W.starProjection x := (hfix _).1 hPmem
  have horth : ∀ w ∈ W, inner ℂ (x - W.starProjection x) w = 0 :=
    Submodule.starProjection_inner_eq_zero (K := W) x
  have happ := hform (x - W.starProjection x) horth
  have hform_eq : (inner ℂ (x - W.starProjection x)
      ((x - W.starProjection x) - K (x - W.starProjection x))).re =
      (inner ℂ x (x - K x)).re := by
    have h1 : (x - W.starProjection x) - K (x - W.starProjection x) =
        (x - K x) - (W.starProjection x - K (W.starProjection x)) := by
      rw [map_sub]
      abel
    have h2 : W.starProjection x - K (W.starProjection x) = 0 := by
      rw [hKP, sub_self]
    have h3 : inner ℂ (W.starProjection x) (K x) =
        inner ℂ (W.starProjection x) x := by
      rw [← hsym (W.starProjection x) x, hKP]
    have h4 : inner ℂ (W.starProjection x) (x - K x) = 0 := by
      rw [inner_sub_right, h3, sub_self]
    rw [h1, h2, sub_zero, inner_sub_left, h4, sub_zero]
  rw [hform_eq] at happ
  calc ‖x - W.starProjection x‖ ^ 2
      = gap⁻¹ * (gap * ‖x - W.starProjection x‖ ^ 2) := by
        rw [inv_mul_cancel_left₀ (ne_of_gt hgap)]
    _ ≤ gap⁻¹ * (inner ℂ x (x - K x)).re :=
        mul_le_mul_of_nonneg_left happ (le_of_lt (inv_pos.mpr hgap))

end CCM24FiniteSGateResidualMomentBricks
end CCM25Concrete
end Source
end ConnesWeilRH
