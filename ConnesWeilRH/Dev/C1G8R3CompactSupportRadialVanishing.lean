/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8R3PositiveRadialTailDecay

/-!
# Compact Support Translation Vanishing for Radial Support Projection

This module formally proves that if a carrier vector `k0 : finiteSCarrier` has upper
support bounded by `R` (vanishes almost everywhere on `(R, ∞)`), then for any translation
parameter `t > R - Real.log lambda`, the radial support projection of
`cc20GlobalLogTranslation t k0` vanishes identically:
`‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection ...‖ = 0`.

Key Theorems:
1. `inner_eq_zero_of_ae_pointwise_zero`:
   If the pointwise inner product vanishes almost everywhere, then `inner ℂ u v = 0`.
2. `inner_eq_zero_of_disjoint_support`:
   If `u` vanishes almost everywhere on `[Real.log lambda, ∞)` and
   `v ∈ ccm24LogRadialSupportClosedSubspace lambda`, then `inner ℂ u v = 0`.
3. `mem_orthogonal_of_ae_eq_zero_on_Ici`:
   If `u` vanishes almost everywhere on `[Real.log lambda, ∞)`, then `u` lies in the
   orthogonal complement `(ccm24LogRadialSupportClosedSubspace lambda).toSubmoduleᗮ`.
4. `starProjection_eq_zero_of_ae_eq_zero_on_Ici`:
   The radial support projection of `u` is identically zero.
5. `norm_starProjection_eq_zero_of_ae_eq_zero_on_Ici`:
   The norm of the radial support projection is zero.
6. `norm_starProjection_translation_eq_zero_of_support_le`:
   For any `k0` supported below `R`, and any `t > R - Real.log lambda`,
   the projection norm is identically zero.
7. `riemannHypothesis_of_right_compact_support_and_hardy_tail_and_aggregateEq`:
   Master Exit to Mathlib `_root_.RiemannHypothesis` where the right wing is discharged
   by compact support vanishing.

Axioms: strictly standard `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ConnesWeilRH
namespace Dev

open MeasureTheory Filter Topology
open ConnesWeilRH.Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CC20YoshidaNearZeros
open Source.C1HealthyYoshidaDetector
open Source.C1SameOwnerWeil
open Source.C1G8AdjointShearGram
open Source.C1G8MasterExit
open Source.C1SemilocalHardyTitchmarshUnitarityReduction

/-- If the pointwise inner product vanishes almost everywhere, then the L2 inner product is zero. -/
theorem inner_eq_zero_of_ae_pointwise_zero
    (u v : cc20GlobalLogCrossingL2)
    (h : (fun t => inner ℂ (u t) (v t)) =ᵐ[volume] 0) :
    inner ℂ u v = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hzero : (fun t => inner ℂ (u t) (v t)) =ᵐ[volume] (fun _ => (0 : ℂ)) := by
    filter_upwards [h] with t ht
    exact ht
  rw [integral_congr_ae hzero, integral_zero]

/-- If `u` vanishes almost everywhere on `[Real.log lambda, ∞)` and `v` is in the radial support subspace,
    their inner product vanishes. -/
theorem inner_eq_zero_of_disjoint_support
    (lambda : CCM24SoninScale) (u v : cc20GlobalLogCrossingL2)
    (hu : ∀ᵐ t ∂volume, Real.log lambda ≤ t → u t = 0)
    (hv : v ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    inner ℂ u v = 0 := by
  have hv_supp := (mem_ccm24LogRadialSupportClosedSubspace_iff lambda v).mp hv
  have hzero : (fun t => inner ℂ (u t) (v t)) =ᵐ[volume] 0 := by
    filter_upwards [hu, hv_supp] with t hut hvt
    change inner ℂ (u t) (v t) = 0
    by_cases ht : t < Real.log lambda
    · rw [hvt ht, inner_zero_right]
    · have hge : Real.log lambda ≤ t := not_lt.mp ht
      rw [hut hge, inner_zero_left]
  exact inner_eq_zero_of_ae_pointwise_zero u v hzero

/-- Any vector vanishing almost everywhere on `[Real.log lambda, ∞)` is orthogonal
    to the radial support subspace. -/
theorem mem_orthogonal_of_ae_eq_zero_on_Ici
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2)
    (hu : ∀ᵐ t ∂volume, Real.log lambda ≤ t → u t = 0) :
    u ∈ (ccm24LogRadialSupportClosedSubspace lambda).toSubmoduleᗮ := by
  rw [Submodule.mem_orthogonal']
  intro v hv
  exact inner_eq_zero_of_disjoint_support lambda u v hu hv

/-- The radial support projection of a vector vanishing on `[Real.log lambda, ∞)` is zero. -/
theorem starProjection_eq_zero_of_ae_eq_zero_on_Ici
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2)
    (hu : ∀ᵐ t ∂volume, Real.log lambda ≤ t → u t = 0) :
    (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection u = 0 := by
  have horth := mem_orthogonal_of_ae_eq_zero_on_Ici lambda u hu
  have hproj : (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.orthogonalProjection u = 0 :=
    Submodule.orthogonalProjection_eq_zero_iff.mpr horth
  rw [Submodule.starProjection_apply, hproj]
  rfl

/-- The norm of the radial support projection of a vector vanishing on `[Real.log lambda, ∞)` is zero. -/
theorem norm_starProjection_eq_zero_of_ae_eq_zero_on_Ici
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2)
    (hu : ∀ᵐ t ∂volume, Real.log lambda ≤ t → u t = 0) :
    ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection u‖ = 0 := by
  rw [starProjection_eq_zero_of_ae_eq_zero_on_Ici lambda u hu, norm_zero]

/-- If `k0` vanishes almost everywhere for `y > R`, then for any translation `t > R - Real.log lambda`,
    the radial support projection norm is identically zero. -/
theorem norm_starProjection_translation_eq_zero_of_support_le
    (lambda : CCM24SoninScale) (k0 : cc20GlobalLogCrossingL2)
    (R : ℝ)
    (hsupp : ∀ᵐ y ∂volume, R < y → k0 y = 0)
    (t : ℝ) (ht : R - Real.log lambda < t) :
    ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
      (cc20GlobalLogTranslation t k0)‖ = 0 := by
  apply norm_starProjection_eq_zero_of_ae_eq_zero_on_Ici
  have hshift := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hsupp
  filter_upwards [cc20GlobalLogTranslation_coeFn t k0, hshift] with x htrans hzero
  intro hx
  rw [htrans]
  have hpos : R < x + t := by linarith
  exact hzero hpos

/-- Master Exit to Mathlib RiemannHypothesis where the right wing is discharged by compact support vanishing. -/
theorem riemannHypothesis_of_right_compact_support_and_hardy_tail_and_aggregateEq
    (hmain : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (ι : Type*)
          (_hcount : Countable ι)
          (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
          (k0 : finiteSCarrier)
          (R : ℝ)
          (hsupp : ∀ᵐ y ∂volume, R < y → k0 y = 0)
          (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
          (hNR : R - Real.log lambda ≤ (N : ℝ))
          (hNpos : 0 < (N : ℝ))
          (C : ℝ) (hC : 0 ≤ C),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
          (∀ i t,
            (rootConvolution owner (sourceInclusion lambda (sourceBasis i)) : ℝ → ℂ) t =
              inner ℂ ((sourceBasis i : sourceSoninCarrier lambda) : finiteSCarrier)
                (cc20GlobalLogTranslation t k0)) ∧
          (∀ s : ℝ, (N : ℝ) < s →
            ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
              (cc20GlobalLogTranslation s (archimedeanHardyTitchmarshOperator k0))‖ ^ 2 ≤ C / s ^ 2) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_vanishing_compact_and_hardy_tail_and_aggregateEq
  intro rho hzero
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, k0, R, hsupp, N, hN, hNR, hNpos, C, hC,
    hdata, hcols, hleft_ht, heq⟩ := hmain rho hzero
  have hvanish : ∀ t : ℝ, (N : ℝ) < t →
      ‖(ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
        (cc20GlobalLogTranslation t k0)‖ = 0 := by
    intro t ht
    have ht' : R - Real.log lambda < t := by linarith
    exact norm_starProjection_translation_eq_zero_of_support_le lambda k0 R hsupp t ht'
  exact ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, k0, N, hN, hNpos, C, hC,
    hdata, hcols, hvanish, hleft_ht, heq⟩

end Dev
end ConnesWeilRH
