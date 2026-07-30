/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
import ConnesWeilRH.Source.CC20Concrete.CCM24RadialHalfLineAlignment

/-!
# Radial split of the antiresonant Bone 1 column

Proof 608 reduces the new-frame restriction of Bone 1 to the single column

```text
primeEulerAmbientLossFactor(p)^dagger * newFrame(S).
```

This module splits that column by the genuine radial-support projection.  The
two pieces are orthogonal.  The exterior piece is exactly a completed
half-line crossing, supported on the finite interval
`[log(lambda) - log(p), log(lambda))`; it has norm at most one before the
ambient-loss scalar is inserted.  The interior piece retains the unresolved
`I + translation_(log p)` antiresonance.

No factorization of the reduced raw row, uniform quotient estimate, Gate 3U
bound, finite-S sign, Burnol identity, or RH conclusion is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit

open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The three exact columns -/

/-- The full antiresonant column on the actual new suffix frame. -/
noncomputable def newFrameAntiresonantColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (primeEulerAmbientLossFactor p)† ∘L newSuffixFrame lambda S

/-- The part of the antiresonant column which remains inside the radial
half-line. -/
noncomputable def newFrameAntiresonantRadialInterior
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L newFrameAntiresonantColumn lambda p S

/-- The part of the antiresonant column which crosses the radial boundary. -/
noncomputable def newFrameAntiresonantRadialBoundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
    newFrameAntiresonantColumn lambda p S

/-- The unscaled completed half-line crossing carried by the boundary part. -/
noncomputable def newFrameAntiresonantRadialBoundaryCrossing
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap ∘L
      newSuffixFrame lambda S

/-! ## The new frame is radial -/

theorem radialSupportProjection_comp_newSuffixFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L newSuffixFrame lambda S =
      newSuffixFrame lambda S := by
  apply ContinuousLinearMap.ext
  intro x
  apply (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
  exact (newSuffixFrame_mem lambda S x).1

theorem radialComplement_comp_newSuffixFrame_eq_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
        newSuffixFrame lambda S = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hfixed := DFunLike.congr_fun
    (radialSupportProjection_comp_newSuffixFrame lambda S) x
  simp only [ContinuousLinearMap.comp_apply] at hfixed
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, hfixed,
    sub_self]

/-! ## Orthogonal decomposition and the completed crossing -/

theorem newFrameAntiresonantColumn_eq_radialInterior_add_boundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    newFrameAntiresonantColumn lambda p S =
      newFrameAntiresonantRadialInterior lambda p S +
        newFrameAntiresonantRadialBoundary lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [newFrameAntiresonantRadialInterior,
    newFrameAntiresonantRadialBoundary, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  abel

/-- The boundary part contains no copy of the identity term.  It is the
ambient square-root scale times one completed radial crossing. -/
theorem newFrameAntiresonantRadialBoundary_eq_scale_smul_crossing
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    newFrameAntiresonantRadialBoundary lambda p S =
      (primeEulerAmbientLossScale p : ℂ) •
        newFrameAntiresonantRadialBoundaryCrossing lambda p S := by
  have hzero := radialComplement_comp_newSuffixFrame_eq_zero lambda S
  rw [newFrameAntiresonantRadialBoundary, newFrameAntiresonantColumn,
    primeEulerAmbientLossFactor_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  have hzeroPoint := DFunLike.congr_fun hzero x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    at hzeroPoint
  simp only [newFrameAntiresonantRadialBoundaryCrossing,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, map_smul,
    map_add]
  rw [hzeroPoint, zero_add]

/-- Pythagorean readback of the two radial pieces. -/
theorem norm_sq_newFrameAntiresonantColumn_eq_radialInterior_add_boundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖newFrameAntiresonantColumn lambda p S x‖ ^ 2 =
      ‖newFrameAntiresonantRadialInterior lambda p S x‖ ^ 2 +
        ‖newFrameAntiresonantRadialBoundary lambda p S x‖ ^ 2 := by
  let radial := (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
  have hpyth := radial.norm_sq_eq_add_norm_sq_starProjection
    (newFrameAntiresonantColumn lambda p S x)
  rw [Submodule.starProjection_orthogonal] at hpyth
  simpa only [radial, radialSupportProjection,
    newFrameAntiresonantRadialInterior,
    newFrameAntiresonantRadialBoundary,
    ContinuousLinearMap.comp_apply] using hpyth

theorem norm_newFrameAntiresonantRadialBoundary_le_full
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖newFrameAntiresonantRadialBoundary lambda p S x‖ ≤
      ‖newFrameAntiresonantColumn lambda p S x‖ := by
  have hpyth :=
    norm_sq_newFrameAntiresonantColumn_eq_radialInterior_add_boundary
      lambda p S x
  nlinarith [norm_nonneg (newFrameAntiresonantColumn lambda p S x),
    norm_nonneg (newFrameAntiresonantRadialInterior lambda p S x),
    norm_nonneg (newFrameAntiresonantRadialBoundary lambda p S x)]

/-! ## Boundary support and norm -/

/-- The unscaled exterior crossing is supported on one literal finite radial
window.  This is where compact root support may legally be used later. -/
theorem newFrameAntiresonantRadialBoundaryCrossing_coeFn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    (newFrameAntiresonantRadialBoundaryCrossing lambda p S x : ℝ → ℂ)
        =ᵐ[volume]
      (Set.Ico (Real.log lambda - Real.log p) (Real.log lambda)).indicator
        (fun t => newSuffixFrame lambda S x (t + Real.log p)) := by
  let u := newSuffixFrame lambda S x
  let shifted := cc20GlobalLogTranslation (Real.log p) u
  have hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda :=
    (newSuffixFrame_mem lambda S x).1
  have huZero :=
    (mem_ccm24LogRadialSupportClosedSubspace_iff lambda u).1 hu
  have huZeroShift :=
    (measurePreserving_add_right volume (Real.log p)).quasiMeasurePreserving.ae
      huZero
  have htranslation := cc20GlobalLogTranslation_coeFn (Real.log p) u
  have hprojection := ccm24TranslatedHalfLineProjection_coeFn lambda shifted
  rw [← ccm24LogRadialSupportProjection_eq_translatedHalfLine] at hprojection
  have hprojection' :
      (radialSupportProjection lambda shifted : ℝ → ℂ) =ᵐ[volume]
        (Set.Ici (Real.log lambda)).indicator (fun t => shifted t) := by
    simpa only [radialSupportProjection] using hprojection
  have hsub := Lp.coeFn_sub shifted (radialSupportProjection lambda shifted)
  filter_upwards [htranslation, hprojection', hsub, huZeroShift] with t
      htranslationAt hprojectionAt hsubAt huZeroAt
  change (shifted - radialSupportProjection lambda shifted : finiteSCarrier) t =
    (Set.Ico (Real.log lambda - Real.log p) (Real.log lambda)).indicator
      (fun s => u (s + Real.log p)) t
  rw [hsubAt]
  simp only [Pi.sub_apply]
  rw [hprojectionAt, htranslationAt]
  by_cases hlow : Real.log lambda - Real.log p ≤ t
  · by_cases hupp : t < Real.log lambda
    · have hwindow : t ∈ Set.Ico (Real.log lambda - Real.log p)
          (Real.log lambda) := ⟨hlow, hupp⟩
      have houtside : t ∉ Set.Ici (Real.log lambda) := by
        exact not_le.mpr hupp
      rw [Set.indicator_of_mem hwindow, Set.indicator_of_notMem houtside,
        sub_zero]
    · have hupp' : Real.log lambda ≤ t := le_of_not_gt hupp
      have houtside : t ∉ Set.Ico (Real.log lambda - Real.log p)
          (Real.log lambda) := by
        intro ht
        exact hupp ht.2
      have hinside : t ∈ Set.Ici (Real.log lambda) := hupp'
      rw [Set.indicator_of_notMem houtside, Set.indicator_of_mem hinside,
        htranslationAt, sub_self]
  · have hbelow : t + Real.log p < Real.log lambda := by linarith
    have hzero := huZeroAt hbelow
    have hnot : t ∉ Set.Ico (Real.log lambda - Real.log p)
        (Real.log lambda) := by
      simp only [Set.mem_Ico, not_and_or]
      exact Or.inl hlow
    have htlt : t < Real.log lambda := by
      have hpLog : 0 ≤ Real.log p :=
        Real.log_nonneg (by exact_mod_cast p.property.le)
      linarith
    have houtside : t ∉ Set.Ici (Real.log lambda) := by
      exact not_le.mpr htlt
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem houtside,
      hzero, sub_zero]

theorem newFrameAntiresonantRadialBoundaryCrossing_norm_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖newFrameAntiresonantRadialBoundaryCrossing lambda p S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  let complement := ContinuousLinearMap.id ℂ finiteSCarrier -
    radialSupportProjection lambda
  have hcomplement : IsStarProjection complement := by
    simpa only [complement] using
      (radialSupportProjection_isStarProjection lambda).one_sub
  calc
    ‖newFrameAntiresonantRadialBoundaryCrossing lambda p S x‖ =
        ‖complement
          (cc20GlobalLogTranslation (Real.log p) (newSuffixFrame lambda S x))‖ := by
      rfl
    _ ≤ ‖cc20GlobalLogTranslation (Real.log p)
          (newSuffixFrame lambda S x)‖ := by
      calc
        ‖complement
            (cc20GlobalLogTranslation (Real.log p)
              (newSuffixFrame lambda S x))‖ ≤
            ‖complement‖ *
              ‖cc20GlobalLogTranslation (Real.log p)
                (newSuffixFrame lambda S x)‖ :=
          complement.le_opNorm _
        _ ≤ 1 *
              ‖cc20GlobalLogTranslation (Real.log p)
                (newSuffixFrame lambda S x)‖ := by
          exact mul_le_mul_of_nonneg_right
            (IsStarProjection.norm_le complement hcomplement)
            (norm_nonneg _)
        _ = ‖cc20GlobalLogTranslation (Real.log p)
              (newSuffixFrame lambda S x)‖ := by ring
    _ = ‖newSuffixFrame lambda S x‖ :=
      norm_cc20GlobalLogTranslation _ _
    _ = ‖x‖ := by
      simpa only [newSuffixFrame] using
        (parameterizedSoninPolarFrame_isometry lambda 1 S (by norm_num) x)
    _ = 1 * ‖x‖ := by ring

theorem newFrameAntiresonantRadialBoundary_norm_le_scale
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖newFrameAntiresonantRadialBoundary lambda p S‖ ≤
      primeEulerAmbientLossScale p := by
  rw [newFrameAntiresonantRadialBoundary_eq_scale_smul_crossing, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeEulerAmbientLossScale_nonneg p)]
  calc
    primeEulerAmbientLossScale p *
        ‖newFrameAntiresonantRadialBoundaryCrossing lambda p S‖ ≤
      primeEulerAmbientLossScale p * 1 := by
        exact mul_le_mul_of_nonneg_left
          (newFrameAntiresonantRadialBoundaryCrossing_norm_le_one lambda p S)
          (primeEulerAmbientLossScale_nonneg p)
    _ = primeEulerAmbientLossScale p := by ring

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
end CCM25Concrete
end Source
end ConnesWeilRH
