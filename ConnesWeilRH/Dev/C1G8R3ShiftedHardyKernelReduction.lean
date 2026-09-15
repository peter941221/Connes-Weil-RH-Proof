/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3RelativeDefectCrossing
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScalePlancherelKernel

/-!
# R3 shifted Hardy kernel reduction

The relative prolate defect is transported to a fixed positive half-line.
This leaf records the exact operator reduction and the resulting conditional
Hilbert--Schmidt interface.  The remaining analytic inputs are deliberately
named: square-summability of the compact-window interior compression and a
strict relative angle for the prolate factor.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.C1SemilocalHardyTitchmarshUnitarityReduction
open Source.CCM25Concrete.SelectedCrossingKernel
open MeasureTheory
open scoped ComplexConjugate FourierTransform

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier
local notation "Jadd" => KernelInterval (-1) 1 0
local notation "Hadd" => ccm24EvenAdditiveL2

noncomputable local instance : CompleteSpace ccm24EvenAdditiveL2 :=
  ccm24EvenAdditiveClosedSubspace.isClosed.completeSpace_coe

/- The expected additive-coordinate kernel for the shifted interior
compression.  The factor `exp b` is the half-density Jacobian and the phase
has the dilation `exp (2*b)`. -/
noncomputable def doubledShiftAdditiveFourierKernel (b : ℝ) :
    ContinuousMap (Jadd × Jadd) ℂ where
  toFun z :=
    (Real.exp b : ℂ) *
      (𝐞 (Real.exp (2 * b) * (z.2.1 * z.1.1)) : ℂ)
  continuous_toFun := by fun_prop

noncomputable def doubledShiftAdditiveIntervalFourierOperator (b : ℝ) :
    Lp ℂ 2 (volume : Measure Jadd) →L[ℂ]
      Lp ℂ 2 (volume : Measure Jadd) :=
  ContinuousKernelHilbertSchmidt.operator
    (volume : Measure Jadd) (volume : Measure Jadd)
    (doubledShiftAdditiveFourierKernel b)

theorem doubledShiftAdditiveFourierKernel_coefficient_eq_scaled_fourierIntegral
    (b : ℝ) (f : ContinuousMap Jadd ℂ) (y : Jadd) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure Jadd) (doubledShiftAdditiveFourierKernel b)
        (ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ f) y =
      ∫ x : Jadd,
        (Real.exp b : ℂ) *
            (𝐞 (-(Real.exp (2 * b) * (x.1 * y.1))) : ℂ) * f x := by
  change inner ℂ
      (ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (doubledShiftAdditiveFourierKernel b) y))
      (ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ f) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards with x
  change f x * star ((Real.exp b : ℂ) *
      (𝐞 (Real.exp (2 * b) * (x.1 * y.1)) : ℂ)) = _
  have hcharacter (r : ℝ) :
      star (𝐞 r : ℂ) = (𝐞 (-r) : ℂ) := by
    rw [AddChar.map_neg_eq_inv (𝐞 : AddChar ℝ Circle) r]
    exact (Circle.coe_inv_eq_conj (𝐞 r)).symm
  have hreal : star (Real.exp b : ℂ) = (Real.exp b : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [star_mul, hcharacter, hreal]
  ring

theorem doubledShiftAdditiveIntervalFourierOperator_summable
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure Jadd)))
    (b : ℝ) :
    Summable fun i =>
      ‖doubledShiftAdditiveIntervalFourierOperator b (basis i)‖ ^ 2 := by
  exact ContinuousKernelHilbertSchmidt.basis_normSq_summable
    (volume : Measure Jadd) (volume : Measure Jadd)
    (doubledShiftAdditiveFourierKernel b) basis

noncomputable def doubledShiftAdditiveFiniteWindowFourierFactor (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  kernelIntervalL2ZeroExtension (-1) 1 0 ∘L
    doubledShiftAdditiveIntervalFourierOperator b ∘L
      globalL2ToKernelInterval (-1) 1 0

theorem doubledShiftAdditiveFiniteWindowFourierFactor_summable
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) (b : ℝ) :
    Summable fun i =>
      ‖doubledShiftAdditiveFiniteWindowFourierFactor b (basis i)‖ ^ 2 := by
  obtain ⟨index, intervalBasis, _⟩ :=
    exists_hilbertBasis (𝕜 := ℂ)
      (E := Lp ℂ 2 (volume : Measure Jadd))
  have hkernel :=
    doubledShiftAdditiveIntervalFourierOperator_summable intervalBasis b
  have hrestrict := PositiveTrace.summable_normSq_precomp
    intervalBasis intervalBasis basis
    (doubledShiftAdditiveIntervalFourierOperator b)
    (globalL2ToKernelInterval (-1) 1 0) hkernel
  exact PositiveTrace.summable_normSq_postcomp basis
    (doubledShiftAdditiveIntervalFourierOperator b ∘L
      globalL2ToKernelInterval (-1) 1 0)
    (kernelIntervalL2ZeroExtension (-1) 1 0) hrestrict

noncomputable def doubledShiftEvenAdditiveFiniteWindowFourierFactor
    (b : ℝ) :
    ccm24EvenAdditiveL2 →L[ℂ] ccm24EvenAdditiveL2 :=
  ccm24EvenSymmetrizationToEven ∘L
    doubledShiftAdditiveFiniteWindowFourierFactor b ∘L
      ccm24EvenAdditiveClosedSubspace.subtypeL

theorem doubledShiftEvenAdditiveFiniteWindowFourierFactor_summable
    {ι : Type*}
    (basis : HilbertBasis ι ℂ ccm24EvenAdditiveL2) (b : ℝ) :
    Summable fun i =>
      ‖doubledShiftEvenAdditiveFiniteWindowFourierFactor b (basis i)‖ ^ 2 := by
  obtain ⟨index, globalBasis, _⟩ :=
    exists_hilbertBasis (𝕜 := ℂ) (E := cc20GlobalLogCrossingL2)
  have hglobal :=
    doubledShiftAdditiveFiniteWindowFourierFactor_summable globalBasis b
  have hrestrict := PositiveTrace.summable_normSq_precomp
    globalBasis globalBasis basis
    (doubledShiftAdditiveFiniteWindowFourierFactor b)
    ccm24EvenAdditiveClosedSubspace.subtypeL hglobal
  exact PositiveTrace.summable_normSq_postcomp basis
    (doubledShiftAdditiveFiniteWindowFourierFactor b ∘L
      ccm24EvenAdditiveClosedSubspace.subtypeL)
    ccm24EvenSymmetrizationToEven hrestrict

noncomputable def doubledShiftHardyInteriorCompression (b : ℝ) : Op :=
  (ContinuousLinearMap.id ℂ Carrier - cc20PositiveHalfLineProjection) ∘L
    doubledShiftHardy b ∘L
      (ContinuousLinearMap.id ℂ Carrier - cc20PositiveHalfLineProjection)

/- The zero-shift anchor is an exact identity, not an asymptotic
comparison: the translated Hardy involution becomes the unit-scale Hardy
operator, so its interior compression is the already aligned unit operator. -/
theorem doubledShiftHardyInteriorCompression_zero_eq_unit :
    doubledShiftHardyInteriorCompression 0 =
      unitInteriorFourierCompression := by
  unfold doubledShiftHardyInteriorCompression
  unfold unitInteriorFourierCompression unitInteriorSupportProjection
  unfold doubledShiftHardy
  unfold archimedeanHardyTitchmarshOperator
  have hzero :
      (cc20GlobalLogTranslation (2 * (0 : ℝ))).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ Carrier := by
    rw [show (2 : ℝ) * 0 = 0 by norm_num]
    exact unitTranslation_zero_operator
  rw [hzero]
  simp

theorem doubledShiftHardyInteriorCompression_zero_summable
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) :
    Summable fun i =>
      ‖doubledShiftHardyInteriorCompression 0 (basis i)‖ ^ 2 := by
  rw [doubledShiftHardyInteriorCompression_zero_eq_unit]
  rw [unitInteriorFourierCompression_summable_iff_evenAdditive basis]
  rw [unitEvenAdditiveFourierCompression_eq_finiteWindowFactor]
  exact unitEvenAdditiveFiniteWindowFourierFactor_summable
    (unitEvenAdditiveBasis basis)

/- The additive dilation induced by logarithmic translation.  This is the
half-density transport of `T_(2*b)`; keeping it as an exact carrier map lets
the remaining kernel theorem be stated entirely on the genuine even additive
owner. -/
noncomputable def doubledShiftEvenAdditiveDilation (b : ℝ) :
    ccm24EvenAdditiveL2 →L[ℂ] ccm24EvenAdditiveL2 :=
  ccm24EvenLogCarrierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
      ccm24EvenLogCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def doubledShiftEvenAdditiveInteriorCompression (b : ℝ) :
    ccm24EvenAdditiveL2 →L[ℂ] ccm24EvenAdditiveL2 :=
  ccm24EvenLogCarrierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    doubledShiftHardyInteriorCompression b ∘L
      ccm24EvenLogCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap

theorem doubledShiftEvenAdditiveInteriorCompression_eq_literal
    (b : ℝ) :
    doubledShiftEvenAdditiveInteriorCompression b =
      unitLiteralEvenAdditiveInteriorProjection ∘L
        doubledShiftEvenAdditiveDilation b ∘L
          ccm24EvenAdditiveFourier.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            unitLiteralEvenAdditiveInteriorProjection := by
  let E : ccm24EvenAdditiveL2 →L[ℂ] Carrier :=
    ccm24EvenLogCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let Ei : Carrier →L[ℂ] ccm24EvenAdditiveL2 :=
    ccm24EvenLogCarrierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let M : Op :=
    ContinuousLinearMap.id ℂ Carrier - cc20PositiveHalfLineProjection
  let T : Op :=
    (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
  let F : ccm24EvenAdditiveL2 →L[ℂ] ccm24EvenAdditiveL2 :=
    ccm24EvenAdditiveFourier.toContinuousLinearEquiv.toContinuousLinearMap
  have hE : E ∘L Ei = ContinuousLinearMap.id ℂ Carrier := by
    apply ContinuousLinearMap.ext
    intro v
    exact ccm24EvenLogCarrierEquiv.apply_symm_apply v
  have hEi : Ei ∘L E = ContinuousLinearMap.id ℂ ccm24EvenAdditiveL2 := by
    apply ContinuousLinearMap.ext
    intro u
    exact ccm24EvenLogCarrierEquiv.symm_apply_apply u
  have hM : Ei ∘L M ∘L E =
      unitLiteralEvenAdditiveInteriorProjection := by
    rw [← unitEvenAdditiveInteriorProjection_eq_literal]
    rfl
  have hH :
      (ccm24ArchimedeanHardyTitchmarsh : Op) = E ∘L F ∘L Ei := by
    apply ContinuousLinearMap.ext
    intro v
    have h := DFunLike.congr_fun
      archimedeanHardyTitchmarshOperator_eq_sourceFourier v
    simpa only [archimedeanHardyTitchmarshOperator,
      ccm24ArchimedeanSourceFourier_apply,
      ContinuousLinearMap.comp_apply, E, Ei, F] using h
  have hD : doubledShiftEvenAdditiveDilation b = Ei ∘L T ∘L E := by
    rfl
  change Ei ∘L (M ∘L T ∘L
      (ccm24ArchimedeanHardyTitchmarsh : Op) ∘L M) ∘L E = _
  rw [hH, hD, ← hM]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  simp [E, Ei, F]

/- The compact-kernel dilation is made explicit on Schwartz data.  This is
the additive-side form of the factor `exp b` and argument dilation `exp (2*b)`
already present in the model kernel. -/
noncomputable def doubledShiftScale (b : ℝ) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (Real.exp (2 * b)) (Real.exp_ne_zero _))

noncomputable def doubledShiftScaledSchwartz (b : ℝ)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (Real.exp b : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (doubledShiftScale b) f

theorem doubledShiftScaledSchwartz_apply
    (b : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    doubledShiftScaledSchwartz b f x =
      (Real.exp b : ℂ) * f (Real.exp (2 * b) * x) := by
  rfl

theorem doubledShiftScaledSchwartz_symmetrization
    (b : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ccm24EvenSchwartzSymmetrizationCLM
        (doubledShiftScaledSchwartz b
          (ccm24EvenSchwartzSymmetrizationCLM f)) x =
      doubledShiftScaledSchwartz b
        (ccm24EvenSchwartzSymmetrizationCLM f) x := by
  rw [ccm24EvenSchwartzSymmetrizationCLM_apply,
    doubledShiftScaledSchwartz_apply,
    doubledShiftScaledSchwartz_apply]
  have heven := ccm24EvenSchwartzSymmetrizationCLM_even f
    (Real.exp (2 * b) * x)
  rw [show Real.exp (2 * b) * -x =
      -(Real.exp (2 * b) * x) by ring, heven]
  ring

theorem doubledShiftEvenAdditiveDilation_bundled
    (b : ℝ) (f : SchwartzMap ℝ ℂ) :
    doubledShiftEvenAdditiveDilation b
        (ccm24BundledEvenSchwartzToEven f) =
      ccm24BundledEvenSchwartzToEven
        (doubledShiftScaledSchwartz b
          (ccm24EvenSchwartzSymmetrizationCLM f)) := by
  apply ccm24EvenLogCarrierEquiv.injective
  unfold doubledShiftEvenAdditiveDilation
  simp only [ContinuousLinearMap.comp_apply]
  change ccm24EvenLogCarrierEquiv
      (ccm24EvenLogCarrierEquiv.symm
        ((cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
          (ccm24EvenLogCarrierEquiv
            (ccm24BundledEvenSchwartzToEven f)))) = _
  rw [ccm24EvenLogCarrierEquiv.apply_symm_apply]
  rw [← ccm24EvenSchwartzToLog_eq_bundled,
    ← ccm24EvenSchwartzToLog_eq_bundled]
  rw [Lp.ext_iff]
  have hleft := cc20GlobalLogTranslation_coeFn (2 * b)
    (ccm24EvenSchwartzToLog f)
  have hleft' :
      ((cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
          (ccm24EvenSchwartzToLog f) : ℝ → ℂ) =ᵐ[volume]
        fun t => (ccm24EvenSchwartzToLog f : ℝ → ℂ) (t + 2 * b) := by
    simpa only using hleft
  have hinput := ccm24EvenSchwartzToLog_coeFn f
  have hinputShift :=
    (measurePreserving_add_right volume (2 * b)).quasiMeasurePreserving.ae_eq
      hinput
  have hright := ccm24EvenSchwartzToLog_coeFn
    (doubledShiftScaledSchwartz b
      (ccm24EvenSchwartzSymmetrizationCLM f))
  filter_upwards [hleft', hinputShift, hright] with t hleftAt hinputAt hrightAt
  simp only [Function.comp_apply] at hinputAt
  rw [hleftAt, hinputAt, hrightAt]
  rw [ccm24NormalizedLogHalfDensityFunction,
    ccm24NormalizedLogHalfDensityFunction]
  rw [doubledShiftScaledSchwartz_symmetrization]
  rw [doubledShiftScaledSchwartz_apply]
  rw [show (t + 2 * b) / 2 = t / 2 + b by ring,
    Real.exp_add]
  simp only [Algebra.smul_def, Complex.ofReal_mul]
  have harg :
      Real.exp (t + 2 * b) = Real.exp (2 * b) * Real.exp t := by
    calc
      Real.exp (t + 2 * b) = Real.exp t * Real.exp (2 * b) := by
        rw [Real.exp_add]
      _ = Real.exp (2 * b) * Real.exp t := by ring
  rw [harg]
  simp only [map_mul, RCLike.algebraMap_eq_ofReal]
  ac_rfl

theorem doubledShiftAdditiveFourierKernel_coefficient_coreProduct
    (b : ℝ) (f : SchwartzMap ℝ ℂ) (y : Jadd) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure Jadd) (doubledShiftAdditiveFourierKernel b)
        (globalL2ToKernelInterval (-1) 1 0
          ((unitFourierCoreProduct f).toLp 2)) y =
      doubledShiftScaledSchwartz b
        (𝓕 (unitFourierCoreProduct f)) y.1 := by
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [doubledShiftAdditiveFourierKernel_coefficient_eq_scaled_fourierIntegral]
  change (∫ x : Jadd,
      (Real.exp b : ℂ) *
          (𝐞 (-(Real.exp (2 * b) * (x.1 * y.1))) : ℂ) *
        unitFourierCoreProduct f x.1 ∂Measure.comap Subtype.val volume) =
    (Real.exp b : ℂ) * (𝓕 (unitFourierCoreProduct f))
      (Real.exp (2 * b) * y.1)
  rw [integral_subtype_comap (μ := (volume : Measure ℝ))
    measurableSet_Icc
    (fun x : ℝ =>
      (Real.exp b : ℂ) *
          (𝐞 (-(Real.exp (2 * b) * (x * y.1))) : ℂ) *
        unitFourierCoreProduct f x)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial, Circle.smul_def, smul_eq_mul]
    have harg : Real.exp (2 * b) * (x * y.1) =
        Real.exp (2 * b) * y.1 * x := by
      ring
    rw [harg]
    ring
  · intro x hx
    have hproduct : unitFourierCoreProduct f x = 0 := by
      by_contra hne
      exact hx (by simpa only [sub_zero, add_zero] using
        unitFourierCoreProduct_support f hne)
    rw [hproduct, mul_zero]

set_option maxHeartbeats 800000 in
theorem doubledShiftAdditiveIntervalFourierOperator_coreProduct
    (b : ℝ) (f : SchwartzMap ℝ ℂ) :
    doubledShiftAdditiveIntervalFourierOperator b
        (globalL2ToKernelInterval (-1) 1 0
          ((unitFourierCoreProduct f).toLp 2)) =
      globalL2ToKernelInterval (-1) 1 0
        ((doubledShiftScaledSchwartz b
          (𝓕 (unitFourierCoreProduct f))).toLp 2) := by
  unfold doubledShiftAdditiveIntervalFourierOperator
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  conv_rhs =>
    rw [globalL2ToKernelInterval_apply_schwartzToLp]
  apply congrArg (ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ)
  ext y
  simpa only [kernelRestriction, Function.comp_apply] using
    doubledShiftAdditiveFourierKernel_coefficient_coreProduct b f y

theorem doubledShiftUnitFourierCoreProduct_symmetrization
    (f : SchwartzMap ℝ ℂ) :
    ccm24EvenSchwartzSymmetrizationCLM (unitFourierCoreProduct f) =
      unitFourierCoreProduct
        (ccm24EvenSchwartzSymmetrizationCLM f) := by
  ext x
  simp only [ccm24EvenSchwartzSymmetrizationCLM_apply,
    unitFourierCoreProduct_apply]
  rw [unitFourierCoreBumpSchwartz_apply,
    unitFourierCoreBumpSchwartz_apply,
    unitFourierCoreBump.neg]
  ring

theorem doubledShiftUnitFourierCoreProduct_even
    (f : SchwartzMap ℝ ℂ) :
    ccm24EvenSchwartzSymmetrizationCLM
        (unitFourierCoreProduct
          (ccm24EvenSchwartzSymmetrizationCLM f)) =
      unitFourierCoreProduct
        (ccm24EvenSchwartzSymmetrizationCLM f) := by
  rw [doubledShiftUnitFourierCoreProduct_symmetrization]
  ext x
  simp only [ccm24EvenSchwartzSymmetrizationCLM_apply,
    unitFourierCoreProduct_apply]
  rw [neg_neg]
  ring

theorem doubledShiftSchwartzFourier_even
    (g : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, g (-x) = g x) (x : ℝ) :
    (𝓕 g) (-x) = (𝓕 g) x := by
  have h := Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) g x
  change 𝓕 (fun y : ℝ => g (-y)) x = (𝓕 g) (-x) at h
  have hfun : (fun y : ℝ => g (-y)) = g := by
    funext y
    exact heven y
  rw [hfun] at h
  exact h.symm

theorem doubledShiftEvenAdditiveFourier_bundledSchwartz
    (f : SchwartzMap ℝ ℂ) :
    ccm24EvenAdditiveFourier
        (ccm24BundledEvenSchwartzToEven f) =
      ccm24BundledEvenSchwartzToEven
        (𝓕 (ccm24EvenSchwartzSymmetrizationCLM f)) := by
  have hsymFourier :
      ccm24EvenSchwartzSymmetrizationCLM
          (𝓕 (ccm24EvenSchwartzSymmetrizationCLM f)) =
        𝓕 (ccm24EvenSchwartzSymmetrizationCLM f) := by
    ext x
    rw [ccm24EvenSchwartzSymmetrizationCLM_apply]
    have heven := ccm24EvenSchwartzSymmetrizationCLM_even f x
    have hfourier := doubledShiftSchwartzFourier_even
      (ccm24EvenSchwartzSymmetrizationCLM f)
      (ccm24EvenSchwartzSymmetrizationCLM_even f) x
    rw [hfourier]
    ring
  apply Subtype.ext
  change Lp.fourierTransformₗᵢ ℝ ℂ
      (ccm24BundledEvenSchwartzToEven f : cc20GlobalLogCrossingL2) =
    (ccm24EvenSchwartzSymmetrizationCLM
      (𝓕 (ccm24EvenSchwartzSymmetrizationCLM f))).toLp 2
  rw [ccm24BundledEvenSchwartzToEven_coe]
  have hFourier :
      Lp.fourierTransformₗᵢ ℝ ℂ
          ((ccm24EvenSchwartzSymmetrizationCLM f).toLp 2) =
        (𝓕 (ccm24EvenSchwartzSymmetrizationCLM f)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq
      (ccm24EvenSchwartzSymmetrizationCLM f)
  rw [hFourier, hsymFourier]

set_option maxHeartbeats 800000 in
theorem doubledShiftEvenAdditiveInteriorCompression_eq_finiteWindowFactor_core
    (b : ℝ) (f : SchwartzMap ℝ ℂ) :
    doubledShiftEvenAdditiveInteriorCompression b
        (ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f)) =
      doubledShiftEvenAdditiveFiniteWindowFourierFactor b
        (ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f)) := by
  rw [doubledShiftEvenAdditiveInteriorCompression_eq_literal]
  unfold doubledShiftEvenAdditiveFiniteWindowFourierFactor
  simp only [ContinuousLinearMap.comp_apply]
  have hprojection :
      unitLiteralEvenAdditiveInteriorProjection
          (ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f)) =
        ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f) := by
    apply Subtype.ext
    rw [unitLiteralEvenAdditiveInteriorProjection_coe,
      ccm24BundledEvenSchwartzToEven_coe,
      doubledShiftUnitFourierCoreProduct_symmetrization]
    exact unitFourierCoreProduct_projection
      (ccm24EvenSchwartzSymmetrizationCLM f)
  rw [hprojection]
  have hfourier := doubledShiftEvenAdditiveFourier_bundledSchwartz
    (unitFourierCoreProduct f)
  have hfourier' := congrArg (doubledShiftEvenAdditiveDilation b) hfourier
  change unitLiteralEvenAdditiveInteriorProjection
      ((doubledShiftEvenAdditiveDilation b)
        (ccm24EvenAdditiveFourier
          (ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f)))) = _
  rw [hfourier']
  rw [doubledShiftEvenAdditiveDilation_bundled]
  have hq :
      ccm24EvenSchwartzSymmetrizationCLM
          (𝓕 (ccm24EvenSchwartzSymmetrizationCLM
            (unitFourierCoreProduct f))) =
        𝓕 (unitFourierCoreProduct
          (ccm24EvenSchwartzSymmetrizationCLM f)) := by
    rw [doubledShiftUnitFourierCoreProduct_symmetrization]
    have hsymFourierCore :
        ccm24EvenSchwartzSymmetrizationCLM
            (𝓕 (unitFourierCoreProduct
              (ccm24EvenSchwartzSymmetrizationCLM f))) =
          𝓕 (unitFourierCoreProduct
            (ccm24EvenSchwartzSymmetrizationCLM f)) := by
      ext x
      rw [ccm24EvenSchwartzSymmetrizationCLM_apply]
      have hcoreEven := doubledShiftUnitFourierCoreProduct_even f
      have hfourier := doubledShiftSchwartzFourier_even
        (unitFourierCoreProduct
          (ccm24EvenSchwartzSymmetrizationCLM f))
        (by
          intro y
          exact (DFunLike.congr_fun hcoreEven (-y)).symm.trans
            ((ccm24EvenSchwartzSymmetrizationCLM_even
              (unitFourierCoreProduct
                (ccm24EvenSchwartzSymmetrizationCLM f)) y).trans
              (DFunLike.congr_fun hcoreEven y))) x
      rw [hfourier]
      ring
    exact hsymFourierCore
  rw [hq]
  let v : ccm24EvenAdditiveL2 :=
    unitLiteralEvenAdditiveInteriorProjection
      (ccm24BundledEvenSchwartzToEven
        (doubledShiftScaledSchwartz b
          (𝓕 (unitFourierCoreProduct
            (ccm24EvenSchwartzSymmetrizationCLM f)))))
  have hu :
      (ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f) :
          cc20GlobalLogCrossingL2) =
        (unitFourierCoreProduct
          (ccm24EvenSchwartzSymmetrizationCLM f)).toLp 2 := by
    rw [ccm24BundledEvenSchwartzToEven_coe,
      doubledShiftUnitFourierCoreProduct_symmetrization]
  have hinterval := doubledShiftAdditiveIntervalFourierOperator_coreProduct b
    (ccm24EvenSchwartzSymmetrizationCLM f)
  have hfactor :
      doubledShiftAdditiveFiniteWindowFourierFactor b
          (ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f) :
            cc20GlobalLogCrossingL2) =
        (v : cc20GlobalLogCrossingL2) := by
    unfold doubledShiftAdditiveFiniteWindowFourierFactor
    simp only [ContinuousLinearMap.comp_apply]
    rw [hu]
    rw [hinterval]
    have hscaled :
        ccm24EvenSchwartzSymmetrizationCLM
            (doubledShiftScaledSchwartz b
              (𝓕 (unitFourierCoreProduct
                (ccm24EvenSchwartzSymmetrizationCLM f)))) =
          doubledShiftScaledSchwartz b
            (𝓕 (unitFourierCoreProduct
              (ccm24EvenSchwartzSymmetrizationCLM f))) := by
      ext x
      rw [ccm24EvenSchwartzSymmetrizationCLM_apply,
        doubledShiftScaledSchwartz_apply]
      rw [doubledShiftScaledSchwartz_apply]
      have hfourier := doubledShiftSchwartzFourier_even
        (unitFourierCoreProduct
          (ccm24EvenSchwartzSymmetrizationCLM f))
        (by
          intro y
          exact (DFunLike.congr_fun (doubledShiftUnitFourierCoreProduct_even f)
            (-y)).symm.trans
            ((ccm24EvenSchwartzSymmetrizationCLM_even
              (unitFourierCoreProduct
                (ccm24EvenSchwartzSymmetrizationCLM f)) y).trans
              (DFunLike.congr_fun (doubledShiftUnitFourierCoreProduct_even f) y)))
        (Real.exp (2 * b) * x)
      rw [show Real.exp (2 * b) * -x =
          -(Real.exp (2 * b) * x) by ring, hfourier]
      ring
    have hv :
        (v : cc20GlobalLogCrossingL2) =
          kernelIntervalL2ZeroExtension (-1) 1 0
            (globalL2ToKernelInterval (-1) 1 0
              ((doubledShiftScaledSchwartz b
                (𝓕 (unitFourierCoreProduct
                  (ccm24EvenSchwartzSymmetrizationCLM f)))).toLp 2)) := by
      dsimp [v]
      rw [unitLiteralEvenAdditiveInteriorProjection_coe,
        unitKernelIntervalProjection_apply,
        ccm24BundledEvenSchwartzToEven_coe,
        hscaled]
    exact hv.symm
  change v = ccm24EvenSymmetrizationToEven
    (doubledShiftAdditiveFiniteWindowFourierFactor b
      (ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f) :
        cc20GlobalLogCrossingL2))
  rw [hfactor, ccm24EvenSymmetrizationToEven_subtype]

/- The finite-window core is dense in the actual projected even carrier after
the interval zero-extension and evenization.  This is the precise density
interface needed to promote the explicit kernel readback from the bump core to
the full carrier; it does not assert density in the unprojected global L2. -/
noncomputable def doubledShiftEvenAdditiveZeroExtension :
    Lp ℂ 2 (volume : Measure Jadd) →L[ℂ] Hadd :=
  ccm24EvenSymmetrizationToEven ∘L
    kernelIntervalL2ZeroExtension (-1) 1 0

theorem doubledShiftEvenAdditiveZeroExtension_coreProduct
    (f : SchwartzMap ℝ ℂ) :
    doubledShiftEvenAdditiveZeroExtension (unitFourierDenseCore f) =
      ccm24BundledEvenSchwartzToEven (unitFourierCoreProduct f) := by
  apply Subtype.ext
  change ccm24EvenSymmetrizationCLM
      (kernelIntervalL2ZeroExtension (-1) 1 0
        (unitFourierDenseCore f)) = _
  rw [unitFourierCoreProduct_zeroExtension,
    ccm24BundledEvenSchwartzToEven_coe]
  rw [unitFourierCoreProduct_projection]
  exact (ccm24EvenSchwartzSymmetrization_toLp
    (unitFourierCoreProduct f)).symm

theorem doubledShiftEvenAdditiveZeroExtension_restrict (u : Hadd) :
    doubledShiftEvenAdditiveZeroExtension
        (globalL2ToKernelInterval (-1) 1 0
          (u : cc20GlobalLogCrossingL2)) =
      unitLiteralEvenAdditiveInteriorProjection u := by
  change ccm24EvenSymmetrizationToEven
      (kernelIntervalL2ZeroExtension (-1) 1 0
        (globalL2ToKernelInterval (-1) 1 0
          (u : cc20GlobalLogCrossingL2))) =
    unitLiteralEvenAdditiveInteriorProjection u
  have hprojection :
      kernelIntervalL2ZeroExtension (-1) 1 0
          (globalL2ToKernelInterval (-1) 1 0
            (u : cc20GlobalLogCrossingL2)) =
        (unitLiteralEvenAdditiveInteriorProjection u :
          cc20GlobalLogCrossingL2) := by
    rw [← unitKernelIntervalProjection_apply,
      unitLiteralEvenAdditiveInteriorProjection_coe]
  rw [hprojection]
  exact ccm24EvenSymmetrizationToEven_subtype _

set_option maxHeartbeats 800000 in
theorem doubledShiftEvenAdditiveInteriorCompression_eq_finiteWindowFactor_on_interval
    (b : ℝ) (w : Lp ℂ 2 (volume : Measure Jadd)) :
    doubledShiftEvenAdditiveInteriorCompression b
        (doubledShiftEvenAdditiveZeroExtension w) =
      doubledShiftEvenAdditiveFiniteWindowFourierFactor b
        (doubledShiftEvenAdditiveZeroExtension w) := by
  refine DenseRange.induction_on unitFourierDenseCore_denseRange w
    (isClosed_eq
      ((doubledShiftEvenAdditiveInteriorCompression b).continuous.comp
        doubledShiftEvenAdditiveZeroExtension.continuous)
      ((doubledShiftEvenAdditiveFiniteWindowFourierFactor b).continuous.comp
        doubledShiftEvenAdditiveZeroExtension.continuous)) ?_
  intro f
  rw [doubledShiftEvenAdditiveZeroExtension_coreProduct]
  exact doubledShiftEvenAdditiveInteriorCompression_eq_finiteWindowFactor_core
    b f

theorem doubledShiftEvenAdditiveInteriorCompression_precomp_projection
    (b : ℝ) (u : Hadd) :
    doubledShiftEvenAdditiveInteriorCompression b u =
      doubledShiftEvenAdditiveInteriorCompression b
        (unitLiteralEvenAdditiveInteriorProjection u) := by
  rw [doubledShiftEvenAdditiveInteriorCompression_eq_literal]
  simp only [ContinuousLinearMap.comp_apply]
  rw [unitLiteralEvenAdditiveInteriorProjection_idempotent]

theorem doubledShiftEvenAdditiveFiniteWindowFourierFactor_restrict_interval
    (b : ℝ) (u : Hadd) :
    doubledShiftEvenAdditiveFiniteWindowFourierFactor b u =
      doubledShiftEvenAdditiveFiniteWindowFourierFactor b
        (unitLiteralEvenAdditiveInteriorProjection u) := by
  unfold doubledShiftEvenAdditiveFiniteWindowFourierFactor
  simp only [ContinuousLinearMap.comp_apply]
  change ccm24EvenSymmetrizationToEven
      (doubledShiftAdditiveFiniteWindowFourierFactor b
        (u : cc20GlobalLogCrossingL2)) =
    ccm24EvenSymmetrizationToEven
      (doubledShiftAdditiveFiniteWindowFourierFactor b
        ((unitLiteralEvenAdditiveInteriorProjection u : Hadd) :
          cc20GlobalLogCrossingL2))
  have hrestriction :
      globalL2ToKernelInterval (-1) 1 0
          (u : cc20GlobalLogCrossingL2) =
        globalL2ToKernelInterval (-1) 1 0
          ((unitLiteralEvenAdditiveInteriorProjection u : Hadd) :
            cc20GlobalLogCrossingL2) := by
    rw [unitLiteralEvenAdditiveInteriorProjection_coe,
      unitKernelIntervalProjection_apply,
      globalL2ToKernelInterval_zeroExtension]
  unfold doubledShiftAdditiveFiniteWindowFourierFactor
  simp only [ContinuousLinearMap.comp_apply]
  rw [hrestriction]

set_option maxHeartbeats 800000 in
theorem doubledShiftEvenAdditiveInteriorCompression_eq_finiteWindowFactor
    (b : ℝ) :
    doubledShiftEvenAdditiveInteriorCompression b =
      doubledShiftEvenAdditiveFiniteWindowFourierFactor b := by
  apply ContinuousLinearMap.ext
  intro u
  let w : Lp ℂ 2 (volume : Measure Jadd) :=
    globalL2ToKernelInterval (-1) 1 0
      (u : cc20GlobalLogCrossingL2)
  have hinterval :=
    doubledShiftEvenAdditiveInteriorCompression_eq_finiteWindowFactor_on_interval
      b w
  have hrestrict : doubledShiftEvenAdditiveZeroExtension w =
      unitLiteralEvenAdditiveInteriorProjection u := by
    dsimp [w]
    exact doubledShiftEvenAdditiveZeroExtension_restrict u
  rw [doubledShiftEvenAdditiveInteriorCompression_precomp_projection b u,
    doubledShiftEvenAdditiveFiniteWindowFourierFactor_restrict_interval b u]
  rw [← hrestrict]
  exact hinterval

theorem doubledShiftEvenAdditiveInteriorCompression_summable
    {ι : Type*} (basis : HilbertBasis ι ℂ Hadd) (b : ℝ) :
    Summable fun i =>
      ‖doubledShiftEvenAdditiveInteriorCompression b (basis i)‖ ^ 2 := by
  rw [doubledShiftEvenAdditiveInteriorCompression_eq_finiteWindowFactor]
  exact doubledShiftEvenAdditiveFiniteWindowFourierFactor_summable basis b

theorem doubledShiftHardyInteriorCompression_eq_evenAdditiveConjugation
    (b : ℝ) :
    doubledShiftHardyInteriorCompression b =
      ccm24EvenLogCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        doubledShiftEvenAdditiveInteriorCompression b ∘L
          ccm24EvenLogCarrierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  unfold doubledShiftEvenAdditiveInteriorCompression
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  simp

theorem doubledShiftHardyInteriorCompression_summable
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) (b : ℝ) :
    Summable fun i =>
      ‖doubledShiftHardyInteriorCompression b (basis i)‖ ^ 2 := by
  have hadditive : Summable fun i =>
      ‖doubledShiftEvenAdditiveInteriorCompression b
        (unitEvenAdditiveBasis basis i)‖ ^ 2 := by
    exact doubledShiftEvenAdditiveInteriorCompression_summable
      (unitEvenAdditiveBasis basis) b
  have hnorm : ∀ i, ‖doubledShiftHardyInteriorCompression b
        (basis i)‖ ^ 2 =
      ‖doubledShiftEvenAdditiveInteriorCompression b
        (unitEvenAdditiveBasis basis i)‖ ^ 2 := by
    intro i
    rw [doubledShiftHardyInteriorCompression_eq_evenAdditiveConjugation]
    simp only [ContinuousLinearMap.comp_apply, unitEvenAdditiveBasis_apply]
    exact congrArg (fun r : ℝ => r ^ 2)
      (ccm24EvenLogCarrierEquiv.norm_map
        (doubledShiftEvenAdditiveInteriorCompression b
          (ccm24EvenLogCarrierEquiv.symm (basis i))))
  exact (summable_congr hnorm).2 hadditive


theorem doubledShiftHardyRawSupportCrossing_eq_neg_interiorCompression
    (b : ℝ) :
    doubledShiftHardyRawSupportCrossing b =
      -(doubledShiftHardyInteriorCompression b ∘L
        doubledShiftHardy b ∘L cc20PositiveHalfLineProjection) := by
  rw [doubledShiftRawSupportCrossing_eq_negative_shiftedHardyWindow b]
  rfl

theorem doubledShiftHardyRawSupportCrossing_summable_of_interiorCompression
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) (b : ℝ)
    (hcompression : Summable fun i =>
      ‖doubledShiftHardyInteriorCompression b (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖doubledShiftHardyRawSupportCrossing b (basis i)‖ ^ 2 := by
  have hpre := PositiveTrace.summable_normSq_precomp
    basis basis basis (doubledShiftHardyInteriorCompression b)
      (doubledShiftHardy b ∘L cc20PositiveHalfLineProjection)
      hcompression
  rw [doubledShiftHardyRawSupportCrossing_eq_neg_interiorCompression b]
  simpa only [ContinuousLinearMap.neg_apply, norm_neg,
    ContinuousLinearMap.comp_assoc] using hpre

theorem doubledShiftRawSupportCrossing_eq_inverse_conjugate
    (b : ℝ) :
    doubledShiftRawSupportCrossing b =
      (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap ∘L
        doubledShiftHardyRawSupportCrossing b ∘L
          (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap := by
  let T : Op := (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
  let Tm : Op := (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap
  have hzero :
      (cc20GlobalLogTranslation 0).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ Carrier :=
    unitTranslation_zero_operator
  have hleft : Tm ∘L T = ContinuousLinearMap.id ℂ Carrier := by
    dsimp [Tm, T]
    calc
      (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap ∘L
          (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap =
          (cc20GlobalLogTranslation (-2 * b + 2 * b)).toContinuousLinearMap := by
            simpa only [ContinuousLinearMap.mul_def] using
              (rawGlobalLogTranslation_comp (-2 * b) (2 * b))
      _ = (cc20GlobalLogTranslation 0).toContinuousLinearMap := by
        congr 2 <;> ring
      _ = ContinuousLinearMap.id ℂ Carrier := hzero
  have hright : T ∘L Tm = ContinuousLinearMap.id ℂ Carrier := by
    dsimp [Tm, T]
    calc
      (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
          (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap =
          (cc20GlobalLogTranslation (2 * b + -2 * b)).toContinuousLinearMap := by
            simpa only [ContinuousLinearMap.mul_def] using
              (rawGlobalLogTranslation_comp (2 * b) (-2 * b))
      _ = (cc20GlobalLogTranslation 0).toContinuousLinearMap := by
        congr 2 <;> ring
      _ = ContinuousLinearMap.id ℂ Carrier := hzero
  have hbridge := doubledShiftRawSupportCrossing_conjugate_eq_shiftedHardyCrossing b
  change doubledShiftRawSupportCrossing b = Tm ∘L
    doubledShiftHardyRawSupportCrossing b ∘L T
  rw [← hbridge]
  calc
    doubledShiftRawSupportCrossing b =
        (ContinuousLinearMap.id ℂ Carrier) ∘L
          doubledShiftRawSupportCrossing b ∘L
            (ContinuousLinearMap.id ℂ Carrier) := by simp
    _ = (Tm ∘L T) ∘L doubledShiftRawSupportCrossing b ∘L
          (Tm ∘L T) := by rw [hleft]
    _ = Tm ∘L (T ∘L doubledShiftRawSupportCrossing b ∘L Tm) ∘L T := by
      simp only [ContinuousLinearMap.comp_assoc]

theorem doubledShiftRawSupportCrossing_summable_of_shifted
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) (b : ℝ)
    (hshifted : Summable fun i =>
      ‖doubledShiftHardyRawSupportCrossing b (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖doubledShiftRawSupportCrossing b (basis i)‖ ^ 2 := by
  rw [doubledShiftRawSupportCrossing_eq_inverse_conjugate b]
  have hpre := PositiveTrace.summable_normSq_precomp
    basis basis basis (doubledShiftHardyRawSupportCrossing b)
      (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap hshifted
  have hpost := PositiveTrace.summable_normSq_postcomp
    basis (doubledShiftHardyRawSupportCrossing b ∘L
      (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap)
      (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap hpre
  simpa only [ContinuousLinearMap.comp_assoc] using hpost

theorem doubledShiftProlateDefectFactor_adjoint_comp_self
    (b : ℝ) :
    (doubledShiftProlateDefectFactor b).adjoint ∘L
        doubledShiftProlateDefectFactor b =
      (doubledShiftProlateHilbertSchmidtFactor b).adjoint ∘L
          doubledShiftProlateHilbertSchmidtFactor b -
        ((doubledShiftProlateHilbertSchmidtFactor b).adjoint ∘L
          doubledShiftProlateHilbertSchmidtFactor b).adjoint ∘L
            (doubledShiftProlateHilbertSchmidtFactor b).adjoint ∘L
              doubledShiftProlateHilbertSchmidtFactor b := by
  let P : Op := doubledShiftRadialProjection b
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  let R : Op := doubledShiftSoninIntersectionProjection b
  let B : Op := P - R
  let A : Op := Q ∘L B
  let D : Op := (ContinuousLinearMap.id ℂ Carrier - B) ∘L A
  have hP : P ∘L P = P := by
    dsimp [P]
    exact (doubledShiftRadialProjection_isStarProjection b).isIdempotentElem
  have hQ : Q ∘L Q = Q := by
    dsimp [Q]
    exact (sourceFourierSupportProjection_isStarProjection unitSoninScale).isIdempotentElem
  have hR : R ∘L R = R := by
    dsimp [R]
    exact (doubledShiftSoninIntersectionProjection_isStarProjection b).isIdempotentElem
  have hPR : P ∘L R = R := by
    dsimp [P, R]
    exact doubledShiftRadialProjection_comp_intersectionProjection b
  have hRP : R ∘L P = R := by
    dsimp [P, R]
    exact intersectionProjection_comp_doubledShiftRadialProjection b
  have hQR : Q ∘L R = R := by
    dsimp [Q, R]
    exact sourceFourierSupportProjection_comp_intersectionProjection b
  have hRQ : R ∘L Q = R := by
    dsimp [Q, R]
    exact intersectionProjection_comp_sourceFourierSupportProjection b
  have hPself : P.adjoint = P := by
    dsimp [P]
    exact (doubledShiftRadialProjection_isStarProjection b).isSelfAdjoint.adjoint_eq
  have hQself : Q.adjoint = Q := by
    dsimp [Q]
    exact (sourceFourierSupportProjection_isStarProjection unitSoninScale).isSelfAdjoint.adjoint_eq
  have hRself : R.adjoint = R := by
    dsimp [R]
    exact (doubledShiftSoninIntersectionProjection_isStarProjection b).isSelfAdjoint.adjoint_eq
  have hB : B ∘L B = B := by
    dsimp [B]
    simp only [ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp]
    rw [hP, hPR, hRP, hR]
    abel
  have hBself : B.adjoint = B := by
    dsimp [B]
    rw [map_sub, hPself, hRself]
  let C : Op := ContinuousLinearMap.id ℂ Carrier - B
  have hCself : C.adjoint = C := by
    dsimp [C]
    rw [map_sub, ContinuousLinearMap.adjoint_id, hBself]
  have hC : C ∘L C = C := by
    dsimp [C]
    simp only [ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp]
    rw [hB]
    abel
  have hAgram : A.adjoint ∘L A = B ∘L Q ∘L B := by
    dsimp [A]
    rw [ContinuousLinearMap.adjoint_comp, hQself, hBself]
    have hQ' := congrArg (fun X : Op => B ∘L X ∘L B) hQ
    simpa only [ContinuousLinearMap.comp_assoc] using hQ'
  have hD_eq : D = C ∘L A := by
    rfl
  have hDgram : D.adjoint ∘L D = B ∘L Q ∘L C ∘L Q ∘L B := by
    rw [hD_eq, ContinuousLinearMap.adjoint_comp]
    rw [hCself]
    calc
      A.adjoint ∘L C ∘L C ∘L A =
          A.adjoint ∘L (C ∘L C) ∘L A := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = A.adjoint ∘L C ∘L A := by rw [hC]
      _ = B ∘L Q ∘L C ∘L Q ∘L B := by
        dsimp [A]
        rw [ContinuousLinearMap.adjoint_comp, hQself, hBself]
        simp only [ContinuousLinearMap.comp_assoc]
  have hKself :
      (A.adjoint ∘L A).adjoint = A.adjoint ∘L A := by
    rw [hAgram]
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, hBself, hQself]
    simp only [ContinuousLinearMap.comp_assoc]
  have hKself' :
      (A.adjoint ∘L A).adjoint = B ∘L Q ∘L B := by
    calc
      (A.adjoint ∘L A).adjoint = A.adjoint ∘L A := hKself
      _ = B ∘L Q ∘L B := hAgram
  change D.adjoint ∘L D = A.adjoint ∘L A -
    (A.adjoint ∘L A).adjoint ∘L (A.adjoint ∘L A)
  rw [hDgram, hKself', hAgram]
  have hQ' : B ∘L Q ∘L Q ∘L B = B ∘L Q ∘L B := by
    have h := congrArg (fun X : Op => B ∘L X ∘L B) hQ
    simpa only [ContinuousLinearMap.comp_assoc] using h
  have hB' :
      (B ∘L Q ∘L B) ∘L (B ∘L Q ∘L B) =
        B ∘L Q ∘L B ∘L Q ∘L B := by
    have h := congrArg (fun X : Op => B ∘L Q ∘L X ∘L Q ∘L B) hB
    simpa only [ContinuousLinearMap.comp_assoc] using h
  dsimp [C]
  simp only [ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.id_comp]
  rw [hQ', hB']

theorem doubledShiftProlateHilbertSchmidtFactor_summable_of_strictAngle
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) (b : ℝ)
    (hangle : ‖doubledShiftProlateHilbertSchmidtFactor b‖ < 1)
    (hraw : Summable fun i =>
      ‖doubledShiftRawSupportCrossing b (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖doubledShiftProlateHilbertSchmidtFactor b (basis i)‖ ^ 2 := by
  have hdefect : Summable fun i =>
      ‖doubledShiftProlateDefectFactor b (basis i)‖ ^ 2 := by
    rw [doubledShiftProlateDefectFactor_eq_rawSupportCrossing b]
    exact hraw
  exact PositiveTrace.summable_normSq_of_strictContraction_of_defect
    basis (doubledShiftProlateHilbertSchmidtFactor b)
      (doubledShiftProlateDefectFactor b) hangle
      (doubledShiftProlateDefectFactor_adjoint_comp_self b) hdefect

theorem doubledShiftProlateHilbertSchmidtFactor_summable_of_strictAngle_and_interiorCompression
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) (b : ℝ)
    (hangle : ‖doubledShiftProlateHilbertSchmidtFactor b‖ < 1)
    (hcompression : Summable fun i =>
      ‖doubledShiftHardyInteriorCompression b (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖doubledShiftProlateHilbertSchmidtFactor b (basis i)‖ ^ 2 := by
  apply doubledShiftProlateHilbertSchmidtFactor_summable_of_strictAngle
    basis b hangle
  apply doubledShiftRawSupportCrossing_summable_of_shifted basis b
  exact doubledShiftHardyRawSupportCrossing_summable_of_interiorCompression
    basis b hcompression

/-- The shifted Hardy involution, viewed as a unitary coordinate change. -/
noncomputable def doubledShiftHardyTranslationEquiv
    (b : ℝ) : Carrier ≃ₗᵢ[ℂ] Carrier :=
  ccm24ArchimedeanHardyTitchmarsh.trans
    (cc20GlobalLogTranslationEquiv (2 * b))

theorem doubledShiftHardyTranslationEquiv_eq (b : ℝ) :
    (doubledShiftHardyTranslationEquiv b : Carrier →L[ℂ] Carrier) =
      doubledShiftHardy b := by
  rfl

theorem doubledShiftHardyTranslationEquiv_symm_apply (b : ℝ) (u : Carrier) :
    (doubledShiftHardyTranslationEquiv b).symm u = doubledShiftHardy b u := by
  apply (doubledShiftHardyTranslationEquiv b).injective
  rw [(doubledShiftHardyTranslationEquiv b).apply_symm_apply]
  have hsq := congrArg (fun L : Op => L u) (doubledShiftHardy_involutive b)
  simpa only [doubledShiftHardyTranslationEquiv_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hsq.symm

noncomputable def doubledShiftCarrierTranslation (b : ℝ) : Op :=
  (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap

noncomputable def doubledShiftCarrierTranslationInv (b : ℝ) : Op :=
  (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap

theorem doubledShiftCarrierTranslation_comp_inv (b : ℝ) :
    doubledShiftCarrierTranslation b ∘L doubledShiftCarrierTranslationInv b =
      ContinuousLinearMap.id ℂ Carrier := by
  dsimp [doubledShiftCarrierTranslation, doubledShiftCarrierTranslationInv]
  have h := rawGlobalLogTranslation_comp (2 * b) (-2 * b)
  have hzero :
      (cc20GlobalLogTranslation 0).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ Carrier := unitTranslation_zero_operator
  rw [show 2 * b + (-2 * b) = 0 by ring, hzero] at h
  simpa only [ContinuousLinearMap.mul_def] using h

theorem doubledShiftCarrierTranslationInv_comp (b : ℝ) :
    doubledShiftCarrierTranslationInv b ∘L doubledShiftCarrierTranslation b =
      ContinuousLinearMap.id ℂ Carrier := by
  dsimp [doubledShiftCarrierTranslation, doubledShiftCarrierTranslationInv]
  have h := rawGlobalLogTranslation_comp (-2 * b) (2 * b)
  have hzero :
      (cc20GlobalLogTranslation 0).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ Carrier := unitTranslation_zero_operator
  rw [show (-2 * b) + 2 * b = 0 by ring, hzero] at h
  simpa only [ContinuousLinearMap.mul_def] using h

/-- Undoing the radial translation returns the radial support to the fixed
positive half-line. -/
theorem doubledShiftCarrierTranslation_conjugate_radial (b : ℝ) :
    doubledShiftCarrierTranslation b ∘L doubledShiftRadialProjection b ∘L
        doubledShiftCarrierTranslationInv b = cc20PositiveHalfLineProjection := by
  simpa only [doubledShiftCarrierTranslation,
    doubledShiftCarrierTranslationInv, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc] using doubledShiftRadialProjection_conjugate b

/-- The same coordinate change turns the unit Fourier support into the Hardy
transported half-line. -/
theorem doubledShiftCarrierTranslation_conjugate_fourier (b : ℝ) :
    doubledShiftCarrierTranslation b ∘L
        sourceFourierSupportProjection unitSoninScale ∘L
          doubledShiftCarrierTranslationInv b =
      cc20TransportedHalfLineProjection (doubledShiftHardyTranslationEquiv b) := by
  apply ContinuousLinearMap.ext
  intro u
  let T := doubledShiftCarrierTranslation b
  let Tm := doubledShiftCarrierTranslationInv b
  let H : Op := ccm24ArchimedeanHardyTitchmarsh
  let P : Op := cc20PositiveHalfLineProjection
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  let K : Op := doubledShiftHardy b
  have hQ : Q = H ∘L P ∘L H := by
    dsimp [Q, H, P]
    simpa only [ContinuousLinearMap.comp_assoc] using
      sourceFourierSupportProjection_unit_eq_hardy_conjugation
  have hHTm : H (Tm u) = T (H u) := by
    have h := archimedeanHardyTitchmarsh_comp_globalLogTranslation (-(2 * b))
    simpa only [T, Tm, doubledShiftCarrierTranslation,
      doubledShiftCarrierTranslationInv, H, ContinuousLinearMap.comp_apply,
      show -(2 * b) = -2 * b by ring,
      show -(-2 * b) = 2 * b by ring] using congrArg (fun L : Op => L u) h
  have hK : K = T ∘L H := by rfl
  change T (Q (Tm u)) = _
  rw [hQ]
  change T (H (P (H (Tm u)))) = _
  rw [hHTm]
  change K (P (K u)) = _
  rw [cc20TransportedHalfLineProjection_apply,
    doubledShiftHardyTranslationEquiv_symm_apply]
  rfl

theorem doubledShiftCarrierTranslation_radial_intertwining (b : ℝ) (u : Carrier) :
    doubledShiftCarrierTranslation b (doubledShiftRadialProjection b u) =
      cc20PositiveHalfLineProjection (doubledShiftCarrierTranslation b u) := by
  have h := congrArg (fun L : Op => L (doubledShiftCarrierTranslation b u))
    (doubledShiftCarrierTranslation_conjugate_radial b)
  have hinv := congrArg (fun L : Op => L u)
    (doubledShiftCarrierTranslationInv_comp b)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hinv h
  rw [hinv] at h
  exact h

theorem doubledShiftCarrierTranslation_fourier_intertwining
    (b : ℝ) (u : Carrier) :
    doubledShiftCarrierTranslation b
        (sourceFourierSupportProjection unitSoninScale u) =
      cc20TransportedHalfLineProjection (doubledShiftHardyTranslationEquiv b)
        (doubledShiftCarrierTranslation b u) := by
  have h := congrArg (fun L : Op => L (doubledShiftCarrierTranslation b u))
    (doubledShiftCarrierTranslation_conjugate_fourier b)
  have hinv := congrArg (fun L : Op => L u)
    (doubledShiftCarrierTranslationInv_comp b)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hinv h
  rw [hinv] at h
  exact h

theorem doubledShiftCarrierTranslationEquiv_symm_eq (b : ℝ) :
    (cc20GlobalLogTranslationEquiv (2 * b)).symm =
      doubledShiftCarrierTranslationInv b := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [doubledShiftCarrierTranslationInv,
    ContinuousLinearMap.coe_coe, show -(2 * b) = -2 * b by ring] using
    globalTranslationContinuousEquiv_symm_apply (2 * b) u

theorem doubledShiftConjugatedIntersection_isStarProjection (b : ℝ) :
    IsStarProjection
      (doubledShiftCarrierTranslation b ∘L
        doubledShiftSoninIntersectionProjection b ∘L
          doubledShiftCarrierTranslationInv b) := by
  let e : Carrier ≃ₗᵢ[ℂ] Carrier := cc20GlobalLogTranslationEquiv (2 * b)
  let U : Op := (e : Carrier →L[ℂ] Carrier)
  let V : Op := (e.symm : Carrier →L[ℂ] Carrier)
  let R : Op := doubledShiftSoninIntersectionProjection b
  let S : Op := U ∘L (R ∘L V)
  have hR : IsIdempotentElem R :=
    (doubledShiftSoninIntersectionProjection_isStarProjection b).isIdempotentElem
  have hRself : IsSelfAdjoint R :=
    (doubledShiftSoninIntersectionProjection_isStarProjection b).isSelfAdjoint
  have hS_idem : IsIdempotentElem S := by
    change (U.comp (R.comp V)).comp (U.comp (R.comp V)) =
      U.comp (R.comp V)
    apply ContinuousLinearMap.ext
    intro u
    have hVU (x : Carrier) : V (U x) = x := by
      change e.symm (e x) = x
      exact e.symm_apply_apply x
    have hR_apply := congrArg (fun A : Op => A (V u)) hR
    simp only [ContinuousLinearMap.comp_apply] at hR_apply ⊢
    rw [hVU]
    simpa using congrArg U hR_apply
  have hS_self : IsSelfAdjoint S := by
    have h := hRself.adjoint_conj V
    simpa only [S, R, U, V, e, LinearIsometryEquiv.adjoint_eq_symm] using h
  have hS : IsStarProjection S := ⟨hS_idem, hS_self⟩
  simpa only [S, R, U, V, e, doubledShiftCarrierTranslationEquiv_symm_eq,
    doubledShiftCarrierTranslation, ContinuousLinearMap.mul_def] using hS

/-- The actual shifted Sonin intersection projection is exactly the standard
intersection after translation. -/
theorem doubledShiftCarrierTranslation_conjugate_intersection (b : ℝ) :
    doubledShiftCarrierTranslation b ∘L
        doubledShiftSoninIntersectionProjection b ∘L
          doubledShiftCarrierTranslationInv b =
      cc20TransportedSoninProjection (doubledShiftHardyTranslationEquiv b) := by
  have hS := doubledShiftConjugatedIntersection_isStarProjection b
  have hG := cc20TransportedSoninProjection_isStarProjection
    (doubledShiftHardyTranslationEquiv b)
  apply ContinuousLinearMap.IsStarProjection.ext hS hG
  apply SetLike.ext
  intro u
  constructor
  · rintro ⟨v, rfl⟩
    rw [cc20TransportedSoninProjection, Submodule.range_starProjection]
    change doubledShiftCarrierTranslation b
        (doubledShiftSoninIntersectionProjection b
          (doubledShiftCarrierTranslationInv b v)) ∈
      (cc20TransportedSoninClosedSubspace
        (doubledShiftHardyTranslationEquiv b)).toSubmodule
    have hw := (doubledShiftSoninClosedSubspace b).toSubmodule.starProjection_apply_mem
      (doubledShiftCarrierTranslationInv b v)
    have hradial := (Submodule.starProjection_eq_self_iff).mpr hw.1
    have hfourier := (Submodule.starProjection_eq_self_iff).mpr hw.2
    change doubledShiftRadialProjection b
        (doubledShiftSoninIntersectionProjection b
          (doubledShiftCarrierTranslationInv b v)) = _ at hradial
    change sourceFourierSupportProjection unitSoninScale
        (doubledShiftSoninIntersectionProjection b
          (doubledShiftCarrierTranslationInv b v)) = _ at hfourier
    have hPfixed : cc20PositiveHalfLineProjection
        (doubledShiftCarrierTranslation b
          (doubledShiftSoninIntersectionProjection b
            (doubledShiftCarrierTranslationInv b v))) =
        doubledShiftCarrierTranslation b
          (doubledShiftSoninIntersectionProjection b
            (doubledShiftCarrierTranslationInv b v)) := by
      have h := doubledShiftCarrierTranslation_radial_intertwining b
        (doubledShiftSoninIntersectionProjection b
          (doubledShiftCarrierTranslationInv b v))
      rw [hradial] at h
      exact h.symm
    have hQfixed : cc20TransportedHalfLineProjection
        (doubledShiftHardyTranslationEquiv b)
        (doubledShiftCarrierTranslation b
          (doubledShiftSoninIntersectionProjection b
            (doubledShiftCarrierTranslationInv b v))) =
        doubledShiftCarrierTranslation b
          (doubledShiftSoninIntersectionProjection b
            (doubledShiftCarrierTranslationInv b v)) := by
      have h := doubledShiftCarrierTranslation_fourier_intertwining b
        (doubledShiftSoninIntersectionProjection b
          (doubledShiftCarrierTranslationInv b v))
      rw [hfourier] at h
      exact h.symm
    change doubledShiftCarrierTranslation b
        (doubledShiftSoninIntersectionProjection b
          (doubledShiftCarrierTranslationInv b v)) ∈ cc20PositiveHalfLineClosedRange ∧
      doubledShiftCarrierTranslation b
        (doubledShiftSoninIntersectionProjection b
          (doubledShiftCarrierTranslationInv b v)) ∈
          cc20TransportedHalfLineClosedRange (doubledShiftHardyTranslationEquiv b)
    constructor
    · change doubledShiftCarrierTranslation b
          (doubledShiftSoninIntersectionProjection b
            (doubledShiftCarrierTranslationInv b v)) ∈
          cc20PositiveHalfLineProjection.range
      exact (mem_range_iff_of_isIdempotentElem cc20PositiveHalfLineProjection
        cc20PositiveHalfLineProjection_isIdempotentElem _).2 hPfixed
    · change doubledShiftCarrierTranslation b
          (doubledShiftSoninIntersectionProjection b
            (doubledShiftCarrierTranslationInv b v)) ∈
        (cc20TransportedHalfLineProjection
          (doubledShiftHardyTranslationEquiv b)).range
      exact (mem_range_iff_of_isIdempotentElem
        (cc20TransportedHalfLineProjection
          (doubledShiftHardyTranslationEquiv b))
        (cc20TransportedHalfLineProjection_isIdempotentElem
          (doubledShiftHardyTranslationEquiv b)) _).2 hQfixed
  · intro hu
    rw [cc20TransportedSoninProjection, Submodule.range_starProjection] at hu
    change u ∈ cc20PositiveHalfLineClosedRange ∧
      u ∈ cc20TransportedHalfLineClosedRange
        (doubledShiftHardyTranslationEquiv b) at hu
    have huP := hu.1
    have huQ := hu.2
    have hPfixed : cc20PositiveHalfLineProjection u = u := by
      change u ∈ cc20PositiveHalfLineProjection.range at huP
      exact (mem_range_iff_of_isIdempotentElem cc20PositiveHalfLineProjection
        cc20PositiveHalfLineProjection_isIdempotentElem _).1 huP
    have hQfixed : cc20TransportedHalfLineProjection
        (doubledShiftHardyTranslationEquiv b) u = u := by
      change u ∈ (cc20TransportedHalfLineProjection
        (doubledShiftHardyTranslationEquiv b)).range at huQ
      exact (mem_range_iff_of_isIdempotentElem
        (cc20TransportedHalfLineProjection
          (doubledShiftHardyTranslationEquiv b))
        (cc20TransportedHalfLineProjection_isIdempotentElem
          (doubledShiftHardyTranslationEquiv b)) _).1 huQ
    have hTmT : doubledShiftCarrierTranslationInv b
        (doubledShiftCarrierTranslation b u) = u := by
      have h := congrArg (fun L : Op => L u)
        (doubledShiftCarrierTranslationInv_comp b)
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    have hTTm : doubledShiftCarrierTranslation b
        (doubledShiftCarrierTranslationInv b u) = u := by
      have h := congrArg (fun L : Op => L u)
        (doubledShiftCarrierTranslation_comp_inv b)
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    have hinjective : Function.Injective (doubledShiftCarrierTranslation b) := by
      intro x y hxy
      change cc20GlobalLogTranslation (2 * b) x =
        cc20GlobalLogTranslation (2 * b) y at hxy
      exact (cc20GlobalLogTranslation (2 * b)).injective hxy
    have hwRadial : doubledShiftRadialProjection b
        (doubledShiftCarrierTranslationInv b u) =
          doubledShiftCarrierTranslationInv b u := by
      apply hinjective
      calc
        doubledShiftCarrierTranslation b
            (doubledShiftRadialProjection b
              (doubledShiftCarrierTranslationInv b u)) =
            cc20PositiveHalfLineProjection
              (doubledShiftCarrierTranslation b
                (doubledShiftCarrierTranslationInv b u)) :=
          doubledShiftCarrierTranslation_radial_intertwining b _
        _ = cc20PositiveHalfLineProjection u := by rw [hTTm]
        _ = u := hPfixed
        _ = doubledShiftCarrierTranslation b
              (doubledShiftCarrierTranslationInv b u) := hTTm.symm
    have hwFourier : sourceFourierSupportProjection unitSoninScale
        (doubledShiftCarrierTranslationInv b u) =
          doubledShiftCarrierTranslationInv b u := by
      apply hinjective
      calc
        doubledShiftCarrierTranslation b
            (sourceFourierSupportProjection unitSoninScale
              (doubledShiftCarrierTranslationInv b u)) =
            cc20TransportedHalfLineProjection
              (doubledShiftHardyTranslationEquiv b)
              (doubledShiftCarrierTranslation b
                (doubledShiftCarrierTranslationInv b u)) :=
          doubledShiftCarrierTranslation_fourier_intertwining b _
        _ = cc20TransportedHalfLineProjection
              (doubledShiftHardyTranslationEquiv b) u := by rw [hTTm]
        _ = u := hQfixed
        _ = doubledShiftCarrierTranslation b
              (doubledShiftCarrierTranslationInv b u) := hTTm.symm
    have hw : doubledShiftCarrierTranslationInv b u ∈
        doubledShiftSoninClosedSubspace b := by
      change doubledShiftCarrierTranslationInv b u ∈
          doubledShiftRadialClosedSubspace b ∧
        doubledShiftCarrierTranslationInv b u ∈
          ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale
      constructor
      · apply (Submodule.starProjection_eq_self_iff).mp
        change doubledShiftRadialProjection b
          (doubledShiftCarrierTranslationInv b u) = _
        exact hwRadial
      · apply (Submodule.starProjection_eq_self_iff).mp
        change sourceFourierSupportProjection unitSoninScale
          (doubledShiftCarrierTranslationInv b u) = _
        exact hwFourier
    have hRfixed : doubledShiftSoninIntersectionProjection b
        (doubledShiftCarrierTranslationInv b u) =
          doubledShiftCarrierTranslationInv b u := by
      change doubledShiftCarrierTranslationInv b u ∈
        doubledShiftSoninClosedSubspace b at hw
      exact (Submodule.starProjection_eq_self_iff).mpr hw
    refine ⟨u, ?_⟩
    change doubledShiftCarrierTranslation b
      (doubledShiftSoninIntersectionProjection b
        (doubledShiftCarrierTranslationInv b u)) = u
    rw [hRfixed, hTTm]

theorem doubledShiftProlateFactor_conjugate (b : ℝ) :
    doubledShiftCarrierTranslation b ∘L
        doubledShiftProlateHilbertSchmidtFactor b ∘L
          doubledShiftCarrierTranslationInv b =
      Source.CC20Concrete.ProlateTraceReduction.prolateFactor
        (doubledShiftHardyTranslationEquiv b) := by
  let T := doubledShiftCarrierTranslation b
  let Tm := doubledShiftCarrierTranslationInv b
  let P : Op := doubledShiftRadialProjection b
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  let R : Op := doubledShiftSoninIntersectionProjection b
  have hTmT : Tm ∘L T = ContinuousLinearMap.id ℂ Carrier :=
    doubledShiftCarrierTranslationInv_comp b
  have hQ := doubledShiftCarrierTranslation_conjugate_fourier b
  have hP := doubledShiftCarrierTranslation_conjugate_radial b
  have hR := doubledShiftCarrierTranslation_conjugate_intersection b
  have hPR : T ∘L (P - R) ∘L Tm =
      cc20PositiveHalfLineProjection -
        cc20TransportedSoninProjection (doubledShiftHardyTranslationEquiv b) := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    rw [hP, hR]
  unfold Source.CC20Concrete.ProlateTraceReduction.prolateFactor
    Source.CC20Concrete.ProlateTraceReduction.supportComplementProjection
  change T ∘L (Q ∘L (P - R)) ∘L Tm = _
  calc
    T ∘L (Q ∘L (P - R)) ∘L Tm =
        (T ∘L Q ∘L Tm) ∘L (T ∘L (P - R) ∘L Tm) := by
          calc
            T ∘L (Q ∘L (P - R)) ∘L Tm =
                T ∘L Q ∘L (Tm ∘L T) ∘L (P - R) ∘L Tm := by
                  rw [hTmT]
                  noncomm_ring
            _ = (T ∘L Q ∘L Tm) ∘L (T ∘L (P - R) ∘L Tm) := by
                  noncomm_ring
    _ = cc20TransportedHalfLineProjection
          (doubledShiftHardyTranslationEquiv b) ∘L
        (cc20PositiveHalfLineProjection -
          cc20TransportedSoninProjection (doubledShiftHardyTranslationEquiv b)) := by
            rw [hQ, hPR]
    _ = Source.CC20Concrete.ProlateTraceReduction.prolateFactor
          (doubledShiftHardyTranslationEquiv b) := by
            rfl

theorem doubledShiftCarrierTranslation_norm_conjugate
    (b : ℝ) (A : Op) :
    ‖doubledShiftCarrierTranslation b ∘L A ∘L
        doubledShiftCarrierTranslationInv b‖ = ‖A‖ := by
  let e : Carrier ≃ₗᵢ[ℂ] Carrier := cc20GlobalLogTranslationEquiv (2 * b)
  have hT : doubledShiftCarrierTranslation b = (e : Op) := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hTm : doubledShiftCarrierTranslationInv b = (e.symm : Op) := by
    exact (doubledShiftCarrierTranslationEquiv_symm_eq b).symm
  rw [hT, hTm]
  calc
    ‖(e : Op) ∘L A ∘L (e.symm : Op)‖ =
        ‖A ∘L (e.symm : Op)‖ := by
          exact e.toLinearIsometry.norm_toContinuousLinearMap_comp
    _ = ‖A‖ :=
      ContinuousLinearMap.opNorm_comp_linearIsometryEquiv A e.symm

theorem doubledShiftProlateHilbertSchmidtFactor_norm_eq_standard (b : ℝ) :
    ‖doubledShiftProlateHilbertSchmidtFactor b‖ =
      ‖Source.CC20Concrete.ProlateTraceReduction.prolateFactor
        (doubledShiftHardyTranslationEquiv b)‖ := by
  calc
    ‖doubledShiftProlateHilbertSchmidtFactor b‖ =
        ‖doubledShiftCarrierTranslation b ∘L
          doubledShiftProlateHilbertSchmidtFactor b ∘L
            doubledShiftCarrierTranslationInv b‖ :=
      (doubledShiftCarrierTranslation_norm_conjugate b
        (doubledShiftProlateHilbertSchmidtFactor b)).symm
    _ = ‖Source.CC20Concrete.ProlateTraceReduction.prolateFactor
          (doubledShiftHardyTranslationEquiv b)‖ := by
      rw [doubledShiftProlateFactor_conjugate]

end Dev
end ConnesWeilRH
