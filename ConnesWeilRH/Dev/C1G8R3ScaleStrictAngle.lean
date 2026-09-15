/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ShiftedHardyKernelReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle

/-!
# R3 moving-scale strict-angle reduction

The unit-scale prolate angle proof is being transported to the actual
doubled-shift family.  This leaf first identifies the scaled even Fourier
compression, proves its compact/self-adjoint/contraction package, and records
the support consequences of an extremal vector.  The analytic support
uniqueness step is the next theorem in this same B5-consumer lane.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open Source.CC20Concrete.ContinuousKernelHilbertSchmidt
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedCrossingKernel
open MeasureTheory
open Complex
open scoped ComplexConjugate FourierTransform

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Hadd" => ccm24EvenAdditiveL2
local notation "Op" => Carrier →L[ℂ] Carrier
local notation "Jadd" => KernelInterval (-1) 1 0

noncomputable local instance : CompleteSpace Hadd :=
  ccm24EvenAdditiveClosedSubspace.isClosed.completeSpace_coe

noncomputable local instance : CompactSpace Jadd := by
  unfold KernelInterval
  infer_instance

/-- The unitary dilation on the even additive carrier induced by logarithmic
translation. -/
noncomputable def doubledShiftEvenAdditiveDilationIsometry (b : ℝ) :
    Hadd ≃ₗᵢ[ℂ] Hadd :=
  ccm24EvenLogCarrierEquiv.trans
    ((cc20GlobalLogTranslationEquiv (2 * b)).trans
      ccm24EvenLogCarrierEquiv.symm)

theorem doubledShiftEvenAdditiveDilationIsometry_toContinuousLinearMap
    (b : ℝ) :
    (doubledShiftEvenAdditiveDilationIsometry b : Hadd →L[ℂ] Hadd) =
      doubledShiftEvenAdditiveDilation b := by
  ext u
  simp [doubledShiftEvenAdditiveDilationIsometry,
    doubledShiftEvenAdditiveDilation, cc20GlobalLogTranslationEquiv]

/-- The scaled additive Fourier transform whose compression is the compact
interior kernel from record 027. -/
noncomputable def doubledShiftEvenAdditiveFourierScale (b : ℝ) :
    Hadd →L[ℂ] Hadd :=
  doubledShiftEvenAdditiveDilation b ∘L
    ccm24EvenAdditiveFourier.toContinuousLinearEquiv.toContinuousLinearMap

theorem doubledShiftEvenAdditiveFourierScale_norm_map
    (b : ℝ) (u : Hadd) :
    ‖doubledShiftEvenAdditiveFourierScale b u‖ = ‖u‖ := by
  rw [doubledShiftEvenAdditiveFourierScale,
    ← doubledShiftEvenAdditiveDilationIsometry_toContinuousLinearMap]
  exact (doubledShiftEvenAdditiveDilationIsometry b).norm_map _ |>.trans
    (ccm24EvenAdditiveFourier.norm_map u)

theorem doubledShiftEvenAdditiveInteriorCompression_isCompactOperator
    (b : ℝ) :
    IsCompactOperator (doubledShiftEvenAdditiveInteriorCompression b) := by
  rw [doubledShiftEvenAdditiveInteriorCompression_eq_finiteWindowFactor]
  have hkernel := operator_isCompactOperator
    (volume : Measure Jadd) (volume : Measure Jadd)
    (doubledShiftAdditiveFourierKernel b)
  have hrestrict := hkernel.comp_clm
    (globalL2ToKernelInterval (-1) 1 0)
  have hzero := hrestrict.clm_comp
    (kernelIntervalL2ZeroExtension (-1) 1 0)
  have heven := hzero.comp_clm
    ccm24EvenAdditiveClosedSubspace.subtypeL
  exact heven.clm_comp ccm24EvenSymmetrizationToEven

theorem doubledShiftHardy_inner_symmetry (b : ℝ) (u v : Carrier) :
    inner ℂ (doubledShiftHardy b u) v =
      inner ℂ u (doubledShiftHardy b v) := by
  have hsq := congrArg (fun L : Op => L v)
    (doubledShiftHardy_involutive b)
  have hK2 : doubledShiftHardy b (doubledShiftHardy b v) = v := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hsq
  calc
    inner ℂ (doubledShiftHardy b u) v =
        inner ℂ (doubledShiftHardy b u)
          (doubledShiftHardy b (doubledShiftHardy b v)) := by
            simpa only [hK2]
    _ = inner ℂ u (doubledShiftHardy b v) := by
          simpa only [doubledShiftHardyTranslationEquiv_eq] using
            (doubledShiftHardyTranslationEquiv b).inner_map_map u
              (doubledShiftHardy b v)

theorem doubledShiftHardyInteriorCompression_isSelfAdjoint (b : ℝ) :
    IsSelfAdjoint (doubledShiftHardyInteriorCompression b) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro u v
  let M : Op := ContinuousLinearMap.id ℂ Carrier -
    cc20PositiveHalfLineProjection
  have hMself : IsSelfAdjoint M := by
    dsimp [M]
    exact (IsSelfAdjoint.one (Carrier →L[ℂ] Carrier)).sub
      cc20PositiveHalfLineProjection_isSelfAdjoint
  have hMsym := hMself.isSymmetric
  change inner ℂ (M (doubledShiftHardy b (M u))) v =
    inner ℂ u (M (doubledShiftHardy b (M v)))
  calc
    inner ℂ (M (doubledShiftHardy b (M u))) v =
        inner ℂ (doubledShiftHardy b (M u)) (M v) := hMsym _ _
    _ = inner ℂ (M u) (doubledShiftHardy b (M v)) :=
      doubledShiftHardy_inner_symmetry b _ _
    _ = inner ℂ u (M (doubledShiftHardy b (M v))) := (hMsym _ _)

theorem doubledShiftEvenAdditiveInteriorCompression_isSelfAdjoint
    (b : ℝ) :
    IsSelfAdjoint (doubledShiftEvenAdditiveInteriorCompression b) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro u v
  have hpoint (x : Hadd) :
      doubledShiftHardyInteriorCompression b
          (ccm24EvenLogCarrierEquiv x) =
        ccm24EvenLogCarrierEquiv
          (doubledShiftEvenAdditiveInteriorCompression b x) := by
    rw [doubledShiftHardyInteriorCompression_eq_evenAdditiveConjugation]
    simp only [ContinuousLinearMap.comp_apply]
    apply congrArg ccm24EvenLogCarrierEquiv
    exact congrArg (doubledShiftEvenAdditiveInteriorCompression b)
      (ccm24EvenLogCarrierEquiv.symm_apply_apply x)
  calc
    inner ℂ (doubledShiftEvenAdditiveInteriorCompression b u) v =
        inner ℂ (ccm24EvenLogCarrierEquiv
          (doubledShiftEvenAdditiveInteriorCompression b u))
          (ccm24EvenLogCarrierEquiv v) := by
            exact (ccm24EvenLogCarrierEquiv.inner_map_map _ _).symm
    _ = inner ℂ (doubledShiftHardyInteriorCompression b
          (ccm24EvenLogCarrierEquiv u))
          (ccm24EvenLogCarrierEquiv v) := by rw [hpoint]
    _ = inner ℂ (ccm24EvenLogCarrierEquiv u)
          (doubledShiftHardyInteriorCompression b
            (ccm24EvenLogCarrierEquiv v)) :=
      (doubledShiftHardyInteriorCompression_isSelfAdjoint b).isSymmetric _ _
    _ = inner ℂ (ccm24EvenLogCarrierEquiv u)
          (ccm24EvenLogCarrierEquiv
            (doubledShiftEvenAdditiveInteriorCompression b v)) := by
              rw [hpoint]
    _ = inner ℂ u (doubledShiftEvenAdditiveInteriorCompression b v) :=
      ccm24EvenLogCarrierEquiv.inner_map_map _ _

theorem unitLiteralEvenAdditiveInteriorProjection_apply_norm_le
    (u : Hadd) :
    ‖unitLiteralEvenAdditiveInteriorProjection u‖ ≤ ‖u‖ := by
  calc
    ‖unitLiteralEvenAdditiveInteriorProjection u‖ ≤
        ‖unitLiteralEvenAdditiveInteriorProjection‖ * ‖u‖ :=
      unitLiteralEvenAdditiveInteriorProjection.le_opNorm u
    _ ≤ 1 * ‖u‖ := by
      gcongr
      exact norm_unitLiteralEvenAdditiveInteriorProjection_le_one
    _ = ‖u‖ := one_mul _

theorem doubledShiftEvenAdditiveInteriorCompression_norm_le_one
    (b : ℝ) :
    ‖doubledShiftEvenAdditiveInteriorCompression b‖ ≤ 1 := by
  rw [doubledShiftEvenAdditiveInteriorCompression_eq_literal b]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  let P := unitLiteralEvenAdditiveInteriorProjection
  calc
    ‖P (doubledShiftEvenAdditiveFourierScale b (P u))‖ ≤
        ‖doubledShiftEvenAdditiveFourierScale b (P u)‖ :=
      unitLiteralEvenAdditiveInteriorProjection_apply_norm_le _
    _ = ‖P u‖ := doubledShiftEvenAdditiveFourierScale_norm_map b _
    _ ≤ ‖u‖ := unitLiteralEvenAdditiveInteriorProjection_apply_norm_le u
    _ = 1 * ‖u‖ := by rw [one_mul]

/-- If the scaled compact Fourier compression has an extremal eigenvector,
both that vector and its scaled Fourier image have the same compact support.
The positive and negative eigenvalue cases are stated separately for direct
use by the compact self-adjoint spectral lemma. -/
theorem doubledShiftEvenAdditiveInteriorCompression_fixed_supports
    (b : ℝ) (u : Hadd)
    (hu : doubledShiftEvenAdditiveInteriorCompression b u = u) :
    unitLiteralEvenAdditiveInteriorProjection u = u ∧
      unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u := by
  have hcompression :
      doubledShiftEvenAdditiveInteriorCompression b u =
        unitLiteralEvenAdditiveInteriorProjection
          (doubledShiftEvenAdditiveFourierScale b
            (unitLiteralEvenAdditiveInteriorProjection u)) := by
    rw [doubledShiftEvenAdditiveInteriorCompression_eq_literal b]
    rfl
  have hnormProjection :
      ‖unitLiteralEvenAdditiveInteriorProjection u‖ = ‖u‖ := by
    have hle := unitLiteralEvenAdditiveInteriorProjection_apply_norm_le
      (doubledShiftEvenAdditiveFourierScale b
        (unitLiteralEvenAdditiveInteriorProjection u))
    rw [← hcompression, hu] at hle
    have hfourierNorm := doubledShiftEvenAdditiveFourierScale_norm_map b
      (unitLiteralEvenAdditiveInteriorProjection u)
    rw [hfourierNorm] at hle
    exact le_antisymm
      (unitLiteralEvenAdditiveInteriorProjection_apply_norm_le u) hle
  have hphysical := unitLiteralEvenAdditiveInteriorProjection_eq_of_norm_eq
    u hnormProjection
  have hfourierNorm :
      ‖unitLiteralEvenAdditiveInteriorProjection
          (doubledShiftEvenAdditiveFourierScale b u)‖ =
        ‖doubledShiftEvenAdditiveFourierScale b u‖ := by
    calc
      ‖unitLiteralEvenAdditiveInteriorProjection
          (doubledShiftEvenAdditiveFourierScale b u)‖ =
          ‖unitLiteralEvenAdditiveInteriorProjection
            (doubledShiftEvenAdditiveFourierScale b
              (unitLiteralEvenAdditiveInteriorProjection u))‖ := by
        rw [hphysical]
      _ = ‖doubledShiftEvenAdditiveInteriorCompression b u‖ := by
        rw [hcompression]
      _ = ‖u‖ := by rw [hu]
      _ = ‖doubledShiftEvenAdditiveFourierScale b u‖ :=
        (doubledShiftEvenAdditiveFourierScale_norm_map b u).symm
  exact ⟨hphysical,
    unitLiteralEvenAdditiveInteriorProjection_eq_of_norm_eq _ hfourierNorm⟩

theorem doubledShiftEvenAdditiveInteriorCompression_negFixed_supports
    (b : ℝ) (u : Hadd)
    (hu : doubledShiftEvenAdditiveInteriorCompression b u = -u) :
    unitLiteralEvenAdditiveInteriorProjection u = u ∧
      unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u := by
  have hcompression :
      doubledShiftEvenAdditiveInteriorCompression b u =
        unitLiteralEvenAdditiveInteriorProjection
          (doubledShiftEvenAdditiveFourierScale b
            (unitLiteralEvenAdditiveInteriorProjection u)) := by
    rw [doubledShiftEvenAdditiveInteriorCompression_eq_literal b]
    rfl
  have hnormProjection :
      ‖unitLiteralEvenAdditiveInteriorProjection u‖ = ‖u‖ := by
    have hle := unitLiteralEvenAdditiveInteriorProjection_apply_norm_le
      (doubledShiftEvenAdditiveFourierScale b
        (unitLiteralEvenAdditiveInteriorProjection u))
    rw [← hcompression, hu, norm_neg] at hle
    have hfourierNorm := doubledShiftEvenAdditiveFourierScale_norm_map b
      (unitLiteralEvenAdditiveInteriorProjection u)
    rw [hfourierNorm] at hle
    exact le_antisymm
      (unitLiteralEvenAdditiveInteriorProjection_apply_norm_le u) hle
  have hphysical := unitLiteralEvenAdditiveInteriorProjection_eq_of_norm_eq
    u hnormProjection
  have hfourierNorm :
      ‖unitLiteralEvenAdditiveInteriorProjection
          (doubledShiftEvenAdditiveFourierScale b u)‖ =
        ‖doubledShiftEvenAdditiveFourierScale b u‖ := by
    calc
      ‖unitLiteralEvenAdditiveInteriorProjection
          (doubledShiftEvenAdditiveFourierScale b u)‖ = ‖-u‖ := by
        calc
          ‖unitLiteralEvenAdditiveInteriorProjection
              (doubledShiftEvenAdditiveFourierScale b u)‖ =
              ‖unitLiteralEvenAdditiveInteriorProjection
                (doubledShiftEvenAdditiveFourierScale b
                  (unitLiteralEvenAdditiveInteriorProjection u))‖ := by
            rw [hphysical]
          _ = ‖doubledShiftEvenAdditiveInteriorCompression b u‖ := by
            rw [hcompression]
          _ = ‖-u‖ := by rw [hu]
      _ = ‖doubledShiftEvenAdditiveFourierScale b u‖ := by
        rw [norm_neg, doubledShiftEvenAdditiveFourierScale_norm_map]
  exact ⟨hphysical,
    unitLiteralEvenAdditiveInteriorProjection_eq_of_norm_eq _ hfourierNorm⟩

theorem unitKernelIntervalProjection_schwartz_eq_zero_of_support_away
    (phi : SchwartzMap ℝ ℂ)
    (hsupport : Function.support phi ⊆
      (Set.Icc (-1 : ℝ) 1)ᶜ) :
    kernelIntervalProjection (-1) 1 0 (phi.toLp 2) = 0 := by
  rw [Lp.ext_iff]
  have hprojection := kernelIntervalProjection_coeFn
    (-1) 1 0 (phi.toLp 2)
  have hphi := phi.coeFn_toLp 2 volume
  filter_upwards
    [hprojection, hphi, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with
      x hprojectionAt hphiAt hzeroAt
  rw [hprojectionAt, hzeroAt]
  simp only [sub_zero, add_zero]
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx, hphiAt]
    by_contra hne
    exact (hsupport hne) hx
  · rw [Set.indicator_of_notMem hx]
    rfl

theorem doubledShiftScaledSchwartz_away_unit_window
    (b : ℝ) (phi : SchwartzMap ℝ ℂ)
    (hsupport : Function.support phi ⊆ Set.Ioi (Real.exp (2 * b))) :
    Function.support
        (doubledShiftScaledSchwartz b
          (ccm24EvenSchwartzSymmetrizationCLM phi)) ⊆
      (Set.Icc (-1 : ℝ) 1)ᶜ := by
  intro x hx
  by_contra hxwindow
  apply hx
  rw [doubledShiftScaledSchwartz_apply]
  have hxwindow' : x ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa only [Set.mem_compl_iff, not_not] using hxwindow
  have hscalePos : 0 < Real.exp (2 * b) := Real.exp_pos _
  have hxlo : -Real.exp (2 * b) ≤ Real.exp (2 * b) * x := by
    calc
      -Real.exp (2 * b) = Real.exp (2 * b) * (-1) := by ring
      _ ≤ Real.exp (2 * b) * x :=
        mul_le_mul_of_nonneg_left hxwindow'.1 hscalePos.le
  have hxhi : Real.exp (2 * b) * x ≤ Real.exp (2 * b) := by
    calc
      Real.exp (2 * b) * x ≤ Real.exp (2 * b) * 1 :=
        mul_le_mul_of_nonneg_left hxwindow'.2 hscalePos.le
      _ = Real.exp (2 * b) := by ring
  have hphi : phi (Real.exp (2 * b) * x) = 0 := by
    by_contra hne
    exact (not_lt_of_ge hxhi) (hsupport hne)
  have hphiNeg : phi (-(Real.exp (2 * b) * x)) = 0 := by
    by_contra hne
    have hxhiNeg : -(Real.exp (2 * b) * x) ≤ Real.exp (2 * b) := by
      linarith
    exact (not_lt_of_ge hxhiNeg) (hsupport hne)
  have hevenZero :
      ccm24EvenSchwartzSymmetrizationCLM phi
          (Real.exp (2 * b) * x) = 0 := by
    rw [ccm24EvenSchwartzSymmetrizationCLM_apply, hphi, hphiNeg]
    simp
  rw [hevenZero]
  simp

theorem ccm24LogSpectralReflectionLinearIsometry_inner_symmetry_dev
    (u v : cc20GlobalLogCrossingL2) :
    inner ℂ (ccm24LogSpectralReflectionLinearIsometry u) v =
      inner ℂ u (ccm24LogSpectralReflectionLinearIsometry v) := by
  calc
    inner ℂ (ccm24LogSpectralReflectionLinearIsometry u) v =
        inner ℂ (ccm24LogSpectralReflectionLinearIsometry u)
          (ccm24LogSpectralReflectionLinearIsometry
            (ccm24LogSpectralReflectionLinearIsometry v)) := by
              rw [ccm24LogSpectralReflection_involutive v]
    _ = inner ℂ u
          (ccm24LogSpectralReflectionLinearIsometry v) :=
      ccm24LogSpectralReflectionLinearIsometry.inner_map_map u _

theorem ccm24LogSpectralReflectionEquiv_inner_symmetry_dev
    (u v : cc20GlobalLogCrossingL2) :
    inner ℂ (ccm24LogSpectralReflection u) v =
      inner ℂ u (ccm24LogSpectralReflection v) := by
  calc
    inner ℂ (ccm24LogSpectralReflection u) v =
        inner ℂ (ccm24LogSpectralReflection u)
          (ccm24LogSpectralReflection
            (ccm24LogSpectralReflection v)) := by
              congr 1
              exact (ccm24LogSpectralReflection_involutive v).symm
    _ = inner ℂ u (ccm24LogSpectralReflection v) :=
      ccm24LogSpectralReflection.inner_map_map u _

theorem ccm24EvenSymmetrizationCLM_inner_symmetry_dev
    (u v : cc20GlobalLogCrossingL2) :
    inner ℂ (ccm24EvenSymmetrizationCLM u) v =
      inner ℂ u (ccm24EvenSymmetrizationCLM v) := by
  rw [ccm24EvenSymmetrizationCLM_apply,
    ccm24EvenSymmetrizationCLM_apply]
  rw [inner_smul_left, inner_add_left,
    inner_smul_right, inner_add_right]
  rw [ccm24LogSpectralReflectionEquiv_inner_symmetry_dev]
  have hcoef : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    change star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹
    simp [Complex.star_def]
  rw [hcoef]

theorem ccm24EvenSchwartzSymmetrizationCLM_idempotent_dev
    (phi : SchwartzMap ℝ ℂ) :
    ccm24EvenSchwartzSymmetrizationCLM
        (ccm24EvenSchwartzSymmetrizationCLM phi) =
      ccm24EvenSchwartzSymmetrizationCLM phi := by
  ext x
  rw [ccm24EvenSchwartzSymmetrizationCLM_apply,
    ccm24EvenSchwartzSymmetrizationCLM_even]
  calc
    (2 : ℂ)⁻¹ *
        (ccm24EvenSchwartzSymmetrizationCLM phi x +
          ccm24EvenSchwartzSymmetrizationCLM phi x) =
        (2 : ℂ)⁻¹ * (2 * ccm24EvenSchwartzSymmetrizationCLM phi x) := by
          rw [← two_mul]
    _ = ccm24EvenSchwartzSymmetrizationCLM phi x := by
      rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul]

theorem doubledShiftScaledFourierEvenTest_inner_eq_zero
    (b : ℝ) (u : Hadd)
    (hscaled : unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u)
    (phi : SchwartzMap ℝ ℂ)
    (hsupport : Function.support phi ⊆ Set.Ioi (Real.exp (2 * b))) :
    inner ℂ (ccm24EvenAdditiveFourier u)
      (ccm24BundledEvenSchwartzToEven
        (ccm24EvenSchwartzSymmetrizationCLM phi)) = 0 := by
  let phiEven := ccm24EvenSchwartzSymmetrizationCLM phi
  let phiScaled := doubledShiftScaledSchwartz b phiEven
  let testBase := ccm24BundledEvenSchwartzToEven phiEven
  let testScaled := ccm24BundledEvenSchwartzToEven phiScaled
  have hscaledEven : ccm24EvenSchwartzSymmetrizationCLM phiScaled = phiScaled := by
    dsimp [phiScaled, phiEven]
    ext x
    exact doubledShiftScaledSchwartz_symmetrization b phi x
  have haway : Function.support phiScaled ⊆ (Set.Icc (-1 : ℝ) 1)ᶜ := by
    simpa only [phiScaled, phiEven] using
      doubledShiftScaledSchwartz_away_unit_window b phi hsupport
  have htestProjection :
      unitLiteralEvenAdditiveInteriorProjection testScaled = 0 := by
    apply Subtype.ext
    rw [unitLiteralEvenAdditiveInteriorProjection_coe,
      ccm24BundledEvenSchwartzToEven_coe, hscaledEven]
    exact unitKernelIntervalProjection_schwartz_eq_zero_of_support_away
      phiScaled haway
  have hscaledPairing :
      inner ℂ (doubledShiftEvenAdditiveFourierScale b u) testScaled = 0 := by
    calc
      inner ℂ (doubledShiftEvenAdditiveFourierScale b u) testScaled =
          inner ℂ
            (unitLiteralEvenAdditiveInteriorProjection
              (doubledShiftEvenAdditiveFourierScale b u)) testScaled := by
                rw [hscaled]
      _ = inner ℂ (doubledShiftEvenAdditiveFourierScale b u)
            (unitLiteralEvenAdditiveInteriorProjection testScaled) :=
          unitLiteralEvenAdditiveInteriorProjection_inner_symmetry _ _
      _ = 0 := by rw [htestProjection]; simp
  have htestDilation : doubledShiftEvenAdditiveDilation b testBase = testScaled := by
    change doubledShiftEvenAdditiveDilation b
        (ccm24BundledEvenSchwartzToEven phiEven) =
      ccm24BundledEvenSchwartzToEven
        (doubledShiftScaledSchwartz b phiEven)
    have hinputEven : ccm24EvenSchwartzSymmetrizationCLM phiEven = phiEven := by
      simpa [phiEven] using
        ccm24EvenSchwartzSymmetrizationCLM_idempotent_dev phi
    exact (doubledShiftEvenAdditiveDilation_bundled b phiEven).trans
      (congrArg ccm24BundledEvenSchwartzToEven
        (congrArg (doubledShiftScaledSchwartz b) hinputEven))
  have htransport :
      inner ℂ
          (doubledShiftEvenAdditiveDilation b (ccm24EvenAdditiveFourier u))
          (doubledShiftEvenAdditiveDilation b testBase) =
        inner ℂ (ccm24EvenAdditiveFourier u) testBase := by
    rw [← doubledShiftEvenAdditiveDilationIsometry_toContinuousLinearMap]
    exact (doubledShiftEvenAdditiveDilationIsometry b).inner_map_map _ _
  have hsame :
      inner ℂ (doubledShiftEvenAdditiveFourierScale b u) testScaled =
        inner ℂ
          (doubledShiftEvenAdditiveDilation b (ccm24EvenAdditiveFourier u))
          (doubledShiftEvenAdditiveDilation b testBase) := by
    change inner ℂ
        (doubledShiftEvenAdditiveDilation b (ccm24EvenAdditiveFourier u))
        testScaled = _
    rw [← htestDilation]
  exact htransport.symm.trans (hsame.symm.trans hscaledPairing)

set_option maxHeartbeats 800000 in
-- The bundled Schwartz-to-L2 equality below crosses the dependent even subtype.
theorem doubledShiftScaledFourier_innerSchwartz_eq_zero
    (b : ℝ) (u : Hadd)
    (hscaled : unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u)
    (phi : SchwartzMap ℝ ℂ)
    (hsupport : Function.support phi ⊆ Set.Ioi (Real.exp (2 * b))) :
    inner ℂ ((ccm24EvenAdditiveFourier u : Hadd) :
        cc20GlobalLogCrossingL2) (phi.toLp 2) = 0 := by
  let phiEven := ccm24EvenSchwartzSymmetrizationCLM phi
  have hEvenPhi : ccm24EvenSchwartzSymmetrizationCLM phiEven = phiEven := by
    simpa [phiEven] using
      ccm24EvenSchwartzSymmetrizationCLM_idempotent_dev phi
  have hbase :
      (ccm24BundledEvenSchwartzToEven phiEven : cc20GlobalLogCrossingL2) =
        ccm24EvenSymmetrizationCLM (phi.toLp 2) := by
    calc
      _ = (ccm24EvenSchwartzSymmetrizationCLM phiEven).toLp 2 :=
        ccm24BundledEvenSchwartzToEven_coe phiEven
      _ = phiEven.toLp 2 := by rw [hEvenPhi]
      _ = ccm24EvenSymmetrizationCLM (phi.toLp 2) :=
        ccm24EvenSchwartzSymmetrization_toLp phi
  have hEvenFourier :
      ccm24EvenSymmetrizationCLM
          ((ccm24EvenAdditiveFourier u : Hadd) : cc20GlobalLogCrossingL2) =
        ((ccm24EvenAdditiveFourier u : Hadd) : cc20GlobalLogCrossingL2) := by
    exact congrArg Subtype.val
      (ccm24EvenSymmetrizationToEven_subtype (ccm24EvenAdditiveFourier u))
  have hpairing := ccm24EvenSymmetrizationCLM_inner_symmetry_dev
    ((ccm24EvenAdditiveFourier u : Hadd) : cc20GlobalLogCrossingL2)
    (phi.toLp 2)
  have hbasePairing :
      inner ℂ ((ccm24EvenAdditiveFourier u : Hadd) :
          cc20GlobalLogCrossingL2)
        (ccm24BundledEvenSchwartzToEven phiEven :
          cc20GlobalLogCrossingL2) = 0 := by
    exact doubledShiftScaledFourierEvenTest_inner_eq_zero
      b u hscaled phi hsupport
  calc
    inner ℂ ((ccm24EvenAdditiveFourier u : Hadd) :
        cc20GlobalLogCrossingL2) (phi.toLp 2) =
      inner ℂ
        (ccm24EvenSymmetrizationCLM
          ((ccm24EvenAdditiveFourier u : Hadd) : cc20GlobalLogCrossingL2))
        (phi.toLp 2) := by rw [hEvenFourier]
    _ = inner ℂ ((ccm24EvenAdditiveFourier u : Hadd) :
          cc20GlobalLogCrossingL2)
        (ccm24EvenSymmetrizationCLM (phi.toLp 2)) := hpairing
    _ = inner ℂ ((ccm24EvenAdditiveFourier u : Hadd) :
          cc20GlobalLogCrossingL2)
        (ccm24BundledEvenSchwartzToEven phiEven :
          cc20GlobalLogCrossingL2) := by rw [← hbase]
    _ = 0 := hbasePairing

theorem doubledShiftScaledFourier_integral_eq_zero
    (b : ℝ) (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hscaled : unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u)
    (phi : SchwartzMap ℝ ℂ)
    (hsupport : Function.support phi ⊆ Set.Ioi (Real.exp (2 * b))) :
    (∫ xi : ℝ,
      inner ℂ (𝓕 (unitSupportedRepresentative u) xi) (phi xi)
        ∂volume) = 0 := by
  have hweak := inner_fourierTransformL2_schwartz_eq_integral_fourier
    (unitSupportedRepresentative u)
    (unitSupportedRepresentative_integrable u)
    (unitSupportedRepresentative_memLp_two u) phi
  rw [unitSupportedRepresentative_toLp_eq u hphysical] at hweak
  have hplancherel :
      Lp.fourierTransformₗᵢ ℝ ℂ
          ((u : Hadd) : cc20GlobalLogCrossingL2) =
        ((ccm24EvenAdditiveFourier u : Hadd) :
          cc20GlobalLogCrossingL2) := rfl
  rw [hplancherel] at hweak
  rw [doubledShiftScaledFourier_innerSchwartz_eq_zero
    b u hscaled phi hsupport] at hweak
  exact hweak.symm

set_option maxHeartbeats 800000 in
-- The local-distribution support test transports the scaled Fourier pairing.
theorem doubledShiftUnitSupportedFourier_eq_zero_on_Ioi
    (b : ℝ) (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hscaled : unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u) :
    Set.EqOn (𝓕 (unitSupportedRepresentative u)) 0
      (Set.Ioi (Real.exp (2 * b))) := by
  let g := unitSupportedRepresentative u
  have hgIntegrable : Integrable g volume :=
    unitSupportedRepresentative_integrable u
  have hfourierContinuous : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hgIntegrable
  have hconjContinuous : Continuous (fun x => conj (𝓕 g x)) :=
    Complex.continuous_conj.comp hfourierContinuous
  have haeConj : ∀ᵐ x ∂volume,
      x ∈ Set.Ioi (Real.exp (2 * b)) → conj (𝓕 g x) = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hconjContinuous.locallyIntegrable.locallyIntegrableOn
        (Set.Ioi (Real.exp (2 * b))) )
    intro test htestDiff htestCompact htestSupport
    let testComplex : ℝ → ℂ := fun x => (test x : ℂ)
    have htestComplexDiff := Complex.ofRealCLM.contDiff.comp htestDiff
    have htestComplexCompact : HasCompactSupport testComplex := by
      exact htestCompact.comp_left (map_zero Complex.ofRealCLM)
    let phi : SchwartzMap ℝ ℂ :=
      htestComplexCompact.toSchwartzMap htestComplexDiff
    have hphiSupport : Function.support phi ⊆
        Set.Ioi (Real.exp (2 * b)) := by
      intro x hx
      apply htestSupport
      apply subset_closure
      change test x ≠ 0
      intro hzero
      apply hx
      simp [phi, testComplex, hzero]
    have hzero := doubledShiftScaledFourier_integral_eq_zero
      b u hphysical hscaled phi hphiSupport
    simpa [g, phi, testComplex, RCLike.inner_apply,
      Complex.star_def, mul_comm] using hzero
  have haeConjRestrict :
      (fun x => conj (𝓕 g x)) =ᵐ[volume.restrict
        (Set.Ioi (Real.exp (2 * b)))] (0 : ℝ → ℂ) := by
    filter_upwards [ae_restrict_of_ae haeConj,
      ae_restrict_mem measurableSet_Ioi] with x hzero hx
    exact hzero hx
  have hconjZero : Set.EqOn (fun x => conj (𝓕 g x)) 0
      (Set.Ioi (Real.exp (2 * b))) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq haeConjRestrict isOpen_Ioi
      hconjContinuous.continuousOn continuous_zero.continuousOn
  intro x hx
  have hxConj := hconjZero hx
  change conj (𝓕 g x) = 0 at hxConj
  have hxConjAgain := congrArg conj hxConj
  simpa using hxConjAgain

theorem doubledShiftUnitSupportedFourier_iteratedDeriv_at
    (b : ℝ) (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hscaled : unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u)
    (a : ℝ) (ha : Real.exp (2 * b) < a) (n : ℕ) :
    iteratedDeriv n (𝓕 (unitSupportedRepresentative u)) a = 0 := by
  have hzero := doubledShiftUnitSupportedFourier_eq_zero_on_Ioi
    b u hphysical hscaled
  have hwithin := iteratedDerivWithin_congr (n := n) hzero ha
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ha] at hwithin
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ha] at hwithin
  simpa using hwithin

set_option maxHeartbeats 800000 in
-- Differentiating the compactly supported Fourier integral yields all moments.
theorem doubledShiftUnitSupportedFourier_moment_eq_zero
    (b : ℝ) (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hscaled : unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u)
    (a : ℝ) (ha : Real.exp (2 * b) < a) (n : ℕ) :
    (∫ x : ℝ, (𝐞 (-(x * a)) : ℂ) * (x : ℂ) ^ n *
      unitSupportedRepresentative u x ∂volume) = 0 := by
  let g := unitSupportedRepresentative u
  have hformula := congrFun
    (Real.iteratedDeriv_fourier
      (f := g) (N := ⊤)
      (fun k _ => unitSupportedRepresentative_moment_integrable u k)
      (n := n) le_top) a
  have hderivZero : iteratedDeriv n (𝓕 g) a = 0 :=
    doubledShiftUnitSupportedFourier_iteratedDeriv_at
      b u hphysical hscaled a ha n
  rw [hderivZero] at hformula
  have hraw :
      𝓕 (fun x : ℝ => (-2 * Real.pi * I * x) ^ n • g x) a = 0 :=
    hformula.symm
  rw [Real.fourier_eq] at hraw
  have hfactor :
      (∫ x : ℝ, 𝐞 (-inner ℝ x a) •
          ((-2 * Real.pi * I * x) ^ n • g x) ∂volume) =
        (-2 * Real.pi * I) ^ n *
          ∫ x : ℝ, (𝐞 (-(x * a)) : ℂ) * (x : ℂ) ^ n * g x
            ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial, Circle.smul_def,
      smul_eq_mul, mul_pow]
    ring
  rw [hfactor] at hraw
  have hconstant : (-2 * Real.pi * I : ℂ) ^ n ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact (mul_eq_zero.mp hraw).resolve_left hconstant

noncomputable def doubledShiftUnitMomentCharacterLInf (a : ℝ) :
    Lp ℂ ⊤ (volume : Measure Jadd) :=
  ContinuousMap.toLp ⊤ (volume : Measure Jadd) ℂ
    ⟨fun x => (𝐞 (x.1 * a) : ℂ), by fun_prop⟩

noncomputable def doubledShiftUnitMomentWitness (a : ℝ) (u : Hadd) :
    Lp ℂ 2 (volume : Measure Jadd) :=
  doubledShiftUnitMomentCharacterLInf a •
    star (globalL2ToKernelInterval (-1) 1 0
      ((u : Hadd) : cc20GlobalLogCrossingL2))

theorem doubledShiftUnitMomentCharacterLInf_coeFn (a : ℝ) :
    (doubledShiftUnitMomentCharacterLInf a : Jadd → ℂ) =ᵐ[volume]
      fun x => (𝐞 (x.1 * a) : ℂ) := by
  exact ContinuousMap.coeFn_toLp (p := ⊤)
    (volume : Measure Jadd)
    ⟨fun x => (𝐞 (x.1 * a) : ℂ), by fun_prop⟩

theorem doubledShiftUnitMomentWitness_coeFn (a : ℝ) (u : Hadd) :
    (doubledShiftUnitMomentWitness a u : Jadd → ℂ) =ᵐ[volume]
      fun x => (𝐞 (x.1 * a) : ℂ) *
        conj ((globalL2ToKernelInterval (-1) 1 0
          ((u : Hadd) : cc20GlobalLogCrossingL2) : Jadd → ℂ) x) := by
  unfold doubledShiftUnitMomentWitness
  filter_upwards
    [Lp.coeFn_lpSMul (r := 2) (doubledShiftUnitMomentCharacterLInf a)
      (star (globalL2ToKernelInterval (-1) 1 0
        ((u : Hadd) : cc20GlobalLogCrossingL2))),
      doubledShiftUnitMomentCharacterLInf_coeFn a,
      Lp.coeFn_star (globalL2ToKernelInterval (-1) 1 0
        ((u : Hadd) : cc20GlobalLogCrossingL2))] with x hmul hcharacter hstar
  rw [hmul]
  change (doubledShiftUnitMomentCharacterLInf a : Jadd → ℂ) x *
      ((star (globalL2ToKernelInterval (-1) 1 0
        ((u : Hadd) : cc20GlobalLogCrossingL2)) :
          Lp ℂ 2 (volume : Measure Jadd)) : Jadd → ℂ) x = _
  rw [hcharacter, hstar]
  rfl

theorem doubledShiftUnitMomentWitness_inner_unitMonomialRow
    (a : ℝ) (u : Hadd) (n : ℕ) :
    inner ℂ (doubledShiftUnitMomentWitness a u) (unitMonomialRow n) =
      ∫ x : ℝ, (𝐞 (-(x * a)) : ℂ) * (x : ℂ) ^ n *
        unitSupportedRepresentative u x ∂volume := by
  rw [L2.inner_def]
  calc
    (∫ x : Jadd,
        inner ℂ ((doubledShiftUnitMomentWitness a u : Jadd → ℂ) x)
          ((unitMonomialRow n : Jadd → ℂ) x) ∂volume) =
        ∫ x : Jadd, (𝐞 (-(x.1 * a)) : ℂ) *
          ((globalL2ToKernelInterval (-1) 1 0
            ((u : Hadd) : cc20GlobalLogCrossingL2) : Jadd → ℂ) x) *
          (x.1 : ℂ) ^ n ∂volume := by
      apply integral_congr_ae
      filter_upwards [doubledShiftUnitMomentWitness_coeFn a u,
        unitMonomialRow_coeFn n] with x hw hrow
      rw [hw, hrow]
      have hcharacterConj : conj (𝐞 (x.1 * a) : ℂ) =
          (𝐞 (-(x.1 * a)) : ℂ) := by
        simp only [← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]
      simp only [RCLike.inner_apply, map_mul, hcharacterConj]
      rw [Complex.conj_conj]
      ring
    _ = ∫ x : ℝ, (𝐞 (-(x * a)) : ℂ) * (x : ℂ) ^ n *
        unitSupportedRepresentative u x ∂volume := by
      have hrestricted := globalL2ToKernelInterval_coeFn
        (-1) 1 0 ((u : Hadd) : cc20GlobalLogCrossingL2)
      apply Eq.trans (integral_congr_ae (hrestricted.mono fun x hx => by
        rw [hx]))
      change (∫ x : Set.Icc (-1 - 0 : ℝ) (1 + 0),
          (𝐞 (-(x.1 * a)) : ℂ) *
          (((u : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) x.1 *
          (x.1 : ℂ) ^ n ∂Measure.comap Subtype.val volume) = _
      rw [integral_subtype_comap (μ := (volume : Measure ℝ))
        measurableSet_Icc
        (fun x : ℝ => (𝐞 (-(x * a)) : ℂ) *
          (((u : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) x *
          (x : ℂ) ^ n)]
      unfold unitSupportedRepresentative
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
      · simp [Set.indicator_of_mem hx]
        ring
      · simp [Set.indicator_of_notMem hx]

theorem doubledShiftUnitMomentWitness_eq_zero_of_supports
    (b : ℝ) (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hscaled : unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u)
    (a : ℝ) (ha : Real.exp (2 * b) < a) :
    doubledShiftUnitMomentWitness a u = 0 := by
  have hrows (n : ℕ) :
      inner ℂ (doubledShiftUnitMomentWitness a u) (unitMonomialRow n) = 0 := by
    rw [doubledShiftUnitMomentWitness_inner_unitMonomialRow]
    exact doubledShiftUnitSupportedFourier_moment_eq_zero
      b u hphysical hscaled a ha n
  have hspan : Submodule.span ℂ (Set.range unitMonomialRow) ≤
      (innerSL ℂ (doubledShiftUnitMomentWitness a u)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hrows n
  apply dense_span_unitMonomialRow.eq_zero_of_inner_left ℂ
  intro v hv
  exact hspan hv

theorem doubledShiftUnitRestrictedVector_eq_zero_of_momentWitness_eq_zero
    (a : ℝ) (u : Hadd)
    (hwitness : doubledShiftUnitMomentWitness a u = 0) :
    globalL2ToKernelInterval (-1) 1 0
        ((u : Hadd) : cc20GlobalLogCrossingL2) = 0 := by
  rw [Lp.ext_iff]
  have hwitnessZero :
      (doubledShiftUnitMomentWitness a u : Jadd → ℂ) =ᵐ[volume]
        (0 : Lp ℂ 2 (volume : Measure Jadd)) := by
    rw [hwitness]
  filter_upwards [doubledShiftUnitMomentWitness_coeFn a u, hwitnessZero,
    Lp.coeFn_zero ℂ 2 (volume : Measure Jadd),
    Lp.coeFn_zero ℂ 2 (volume : Measure Jadd)] with
      x hw hzero hzeroWitness hzeroTarget
  rw [hzeroWitness] at hzero
  rw [hzeroTarget]
  rw [hw] at hzero
  have hcharacter : (𝐞 (x.1 * a) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hconj := (mul_eq_zero.mp hzero).resolve_left hcharacter
  have hconjAgain := congrArg conj hconj
  simpa using hconjAgain

theorem doubledShiftEvenAdditiveInteriorCompression_no_extremizers
    (b : ℝ) (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hscaled : unitLiteralEvenAdditiveInteriorProjection
        (doubledShiftEvenAdditiveFourierScale b u) =
          doubledShiftEvenAdditiveFourierScale b u) :
    u = 0 := by
  let a := Real.exp (2 * b) + 1
  have ha : Real.exp (2 * b) < a := by
    dsimp [a]
    linarith
  have hwitness := doubledShiftUnitMomentWitness_eq_zero_of_supports
    b u hphysical hscaled a ha
  have hrestricted :=
    doubledShiftUnitRestrictedVector_eq_zero_of_momentWitness_eq_zero
      a u hwitness
  apply Subtype.ext
  change ((u : Hadd) : cc20GlobalLogCrossingL2) = 0
  calc
    ((u : Hadd) : cc20GlobalLogCrossingL2) =
        kernelIntervalProjection (-1) 1 0
          ((u : Hadd) : cc20GlobalLogCrossingL2) := by
      rw [← unitLiteralEvenAdditiveInteriorProjection_coe, hphysical]
    _ = kernelIntervalL2ZeroExtension (-1) 1 0
        (globalL2ToKernelInterval (-1) 1 0
          ((u : Hadd) : cc20GlobalLogCrossingL2)) :=
      unitKernelIntervalProjection_apply _
    _ = 0 := by rw [hrestricted]; simp

theorem doubledShiftEvenAdditiveInteriorCompression_norm_lt_one
    (b : ℝ) :
    ‖doubledShiftEvenAdditiveInteriorCompression b‖ < 1 := by
  apply norm_lt_one_of_compact_selfAdjoint_of_no_fixed_vectors
    (doubledShiftEvenAdditiveInteriorCompression b)
    (doubledShiftEvenAdditiveInteriorCompression_isCompactOperator b)
    (doubledShiftEvenAdditiveInteriorCompression_isSelfAdjoint b)
    (doubledShiftEvenAdditiveInteriorCompression_norm_le_one b)
  · intro u hu
    have hsupports :=
      doubledShiftEvenAdditiveInteriorCompression_fixed_supports b u hu
    exact doubledShiftEvenAdditiveInteriorCompression_no_extremizers
      b u hsupports.1 hsupports.2
  · intro u hu
    have hsupports :=
      doubledShiftEvenAdditiveInteriorCompression_negFixed_supports b u hu
    exact doubledShiftEvenAdditiveInteriorCompression_no_extremizers
      b u hsupports.1 hsupports.2

end Dev
end ConnesWeilRH
