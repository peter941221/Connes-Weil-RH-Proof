import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Unit-scale Plancherel and compact Fourier-kernel identification

This module identifies Mathlib's genuine `L2` Plancherel compression on the
additive unit interval with the continuous compact-kernel operator constructed
in `CCM24UnitScaleProlateTraceReduction`.  The proof uses a dense core obtained
by multiplying restricted Schwartz functions by a smooth bump supported in
the open unit interval, so zero extension remains a genuine Schwartz function.
-/

namespace ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction

open MeasureTheory
open scoped ContDiff FourierTransform
open CC20Concrete
open CC20Concrete.ContinuousKernelHilbertSchmidt
open CCM24FiniteSProjectionTrace
open SelectedCrossingKernel
open SelectedCrossingOperatorBridge

local notation "Jadd" => KernelInterval (-1) 1 0
local notation "Hadd" => ccm24EvenAdditiveL2
local notation "H" => finiteSCarrier

noncomputable def unitFourierCoreBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def unitFourierCoreBumpFunction : ℝ → ℂ :=
  fun x => Complex.ofRealCLM (unitFourierCoreBump x)

theorem unitFourierCoreBumpFunction_hasCompactSupport :
    HasCompactSupport unitFourierCoreBumpFunction := by
  exact unitFourierCoreBump.hasCompactSupport.comp_left (map_zero _)

theorem unitFourierCoreBumpFunction_contDiff :
    ContDiff ℝ ∞ unitFourierCoreBumpFunction := by
  exact Complex.ofRealCLM.contDiff.comp unitFourierCoreBump.contDiff

noncomputable def unitFourierCoreBumpSchwartz : SchwartzMap ℝ ℂ :=
  unitFourierCoreBumpFunction_hasCompactSupport.toSchwartzMap
    unitFourierCoreBumpFunction_contDiff

theorem unitFourierCoreBumpSchwartz_apply (x : ℝ) :
    unitFourierCoreBumpSchwartz x = unitFourierCoreBump x := rfl

noncomputable def unitFourierCoreBumpIntervalLInf :
    Lp ℂ ⊤ (volume : Measure Jadd) :=
  ContinuousMap.toLp ⊤ (volume : Measure Jadd) ℂ
    ⟨fun x => unitFourierCoreBumpSchwartz x.1, by fun_prop⟩

noncomputable def unitFourierCoreBumpMultiplier :
    Lp ℂ 2 (volume : Measure Jadd) →L[ℂ]
      Lp ℂ 2 (volume : Measure Jadd) := by
  let multiplier := unitFourierCoreBumpIntervalLInf
  let linear : Lp ℂ 2 (volume : Measure Jadd) →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure Jadd) :=
    { toFun := fun u => multiplier • u
      map_add' := fun u v => Lp.add_smul multiplier u v
      map_smul' := fun c u => (Lp.smul_comm c multiplier u).symm }
  exact LinearMap.mkContinuous linear ‖multiplier‖ fun u =>
    Lp.norm_smul_le multiplier u

theorem unitFourierCoreBumpMultiplier_apply
    (u : Lp ℂ 2 (volume : Measure Jadd)) :
    unitFourierCoreBumpMultiplier u =
      unitFourierCoreBumpIntervalLInf • u := rfl

theorem unitFourierCoreBumpIntervalLInf_coeFn :
    (unitFourierCoreBumpIntervalLInf : Jadd → ℂ) =ᵐ[volume]
      fun x => unitFourierCoreBumpSchwartz x.1 := by
  exact ContinuousMap.coeFn_toLp (p := ⊤)
    (volume : Measure Jadd)
    ⟨fun x => unitFourierCoreBumpSchwartz x.1, by fun_prop⟩

theorem unitFourierCoreBumpMultiplier_coeFn
    (u : Lp ℂ 2 (volume : Measure Jadd)) :
    (unitFourierCoreBumpMultiplier u : Jadd → ℂ) =ᵐ[volume]
      fun x => unitFourierCoreBumpSchwartz x.1 * u x := by
  rw [unitFourierCoreBumpMultiplier_apply]
  filter_upwards
    [Lp.coeFn_lpSMul (r := 2) unitFourierCoreBumpIntervalLInf u,
      unitFourierCoreBumpIntervalLInf_coeFn] with x hmul hbump
  rw [hmul]
  change (unitFourierCoreBumpIntervalLInf : Jadd → ℂ) x * u x = _
  rw [hbump]

theorem unitFourierCoreBumpMultiplier_inner_symmetry
    (u v : Lp ℂ 2 (volume : Measure Jadd)) :
    inner ℂ (unitFourierCoreBumpMultiplier u) v =
      inner ℂ u (unitFourierCoreBumpMultiplier v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [unitFourierCoreBumpMultiplier_coeFn u,
      unitFourierCoreBumpMultiplier_coeFn v] with x hu hv
  rw [hu, hv]
  have hbumpStar : (starRingEnd ℂ) (unitFourierCoreBumpSchwartz x.1) =
      unitFourierCoreBumpSchwartz x.1 := by
    change star (unitFourierCoreBumpSchwartz x.1) = _
    rw [unitFourierCoreBumpSchwartz_apply]
    rw [Complex.star_def]
    exact Complex.conj_ofReal _
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, hbumpStar]
  ring

theorem unitFourierCoreBumpMultiplier_isSelfAdjoint :
    IsSelfAdjoint unitFourierCoreBumpMultiplier := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  exact unitFourierCoreBumpMultiplier_inner_symmetry

theorem unitFourierCoreBumpMultiplier_ker_eq_bot :
    unitFourierCoreBumpMultiplier.ker = ⊥ := by
  apply le_antisymm
  · intro u hu
    change u = 0
    change unitFourierCoreBumpMultiplier u = 0 at hu
    rw [Lp.ext_iff]
    have hleft : ∀ᵐ x : Jadd ∂volume, x.1 ≠ -1 := by
      have hsource : ∀ᵐ x : ℝ
          ∂(volume.restrict (Set.Icc (-1 - 0 : ℝ) (1 + 0))),
          x ≠ -1 := by
        simpa only [sub_zero, add_zero] using
          (ae_restrict_of_ae (s := Set.Icc (-1 : ℝ) 1)
            (MeasureTheory.volume.ae_ne (-1 : ℝ)))
      exact (measurePreserving_kernelIntervalSubtypeVal (-1) 1 0)
        |>.quasiMeasurePreserving.ae hsource
    have hright : ∀ᵐ x : Jadd ∂volume, x.1 ≠ 1 := by
      have hsource : ∀ᵐ x : ℝ
          ∂(volume.restrict (Set.Icc (-1 - 0 : ℝ) (1 + 0))),
          x ≠ 1 := by
        simpa only [sub_zero, add_zero] using
          (ae_restrict_of_ae (s := Set.Icc (-1 : ℝ) 1)
            (MeasureTheory.volume.ae_ne (1 : ℝ)))
      exact (measurePreserving_kernelIntervalSubtypeVal (-1) 1 0)
        |>.quasiMeasurePreserving.ae hsource
    have hzero : (unitFourierCoreBumpMultiplier u : Jadd → ℂ) =ᵐ[volume]
        (0 : Lp ℂ 2 (volume : Measure Jadd)) := by
      rw [hu]
    filter_upwards
      [unitFourierCoreBumpMultiplier_coeFn u, hzero,
        Lp.coeFn_zero ℂ 2 (volume : Measure Jadd),
        hleft, hright] with
        x hmul hzeroAt hzeroCoe hxneLeft hxneRight
    rw [hzeroCoe] at hzeroAt
    have hxmem : -1 ≤ x.1 ∧ x.1 ≤ 1 := by
      have hx := x.property
      change -1 - 0 ≤ x.1 ∧ x.1 ≤ 1 + 0 at hx
      norm_num at hx ⊢
      exact hx
    have hxball : x.1 ∈ Metric.ball (0 : ℝ) 1 := by
      rw [Metric.mem_ball, Real.dist_eq]
      simp only [sub_zero]
      exact abs_lt.mpr
        ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hxneLeft),
          lt_of_le_of_ne hxmem.2 hxneRight⟩
    have hbump : unitFourierCoreBumpSchwartz x.1 ≠ 0 := by
      rw [unitFourierCoreBumpSchwartz_apply]
      exact Complex.ofReal_ne_zero.mpr
        (unitFourierCoreBump.pos_of_mem_ball hxball).ne'
    rw [hmul] at hzeroAt
    rw [hzeroCoe]
    exact (mul_eq_zero.mp hzeroAt).resolve_left hbump
  · exact bot_le

theorem unitFourierCoreBumpMultiplier_denseRange :
    DenseRange unitFourierCoreBumpMultiplier := by
  have horthogonal : unitFourierCoreBumpMultiplier.rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range]
    rw [unitFourierCoreBumpMultiplier_isSelfAdjoint.adjoint_eq]
    exact unitFourierCoreBumpMultiplier_ker_eq_bot
  have hclosure : unitFourierCoreBumpMultiplier.range.topologicalClosure = ⊤ := by
    apply (Submodule.orthogonal_eq_bot_iff.mp ?_)
    rw [Submodule.orthogonal_closure]
    exact horthogonal
  rw [DenseRange, dense_iff_closure_eq]
  change closure
      (unitFourierCoreBumpMultiplier.range :
        Set (Lp ℂ 2 (volume : Measure Jadd))) = Set.univ
  rw [← Submodule.topologicalClosure_coe, hclosure]
  rfl

noncomputable def unitFourierCoreRestriction :
    SchwartzMap ℝ ℂ →L[ℂ] Lp ℂ 2 (volume : Measure Jadd) :=
  globalL2ToKernelInterval (-1) 1 0 ∘L
    SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume

theorem unitFourierCoreRestriction_denseRange :
    DenseRange unitFourierCoreRestriction := by
  have hschwartz : DenseRange
      (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
      (p := (2 : ENNReal))
      (by norm_num)
  have hrestriction : DenseRange
      (globalL2ToKernelInterval (-1) 1 0) :=
    (surjective_globalL2ToKernelInterval (-1) 1 0).denseRange
  exact hrestriction.comp hschwartz
    (globalL2ToKernelInterval (-1) 1 0).continuous

noncomputable def unitFourierDenseCore :
    SchwartzMap ℝ ℂ →L[ℂ] Lp ℂ 2 (volume : Measure Jadd) :=
  unitFourierCoreBumpMultiplier ∘L unitFourierCoreRestriction

theorem unitFourierDenseCore_denseRange :
    DenseRange unitFourierDenseCore := by
  exact unitFourierCoreBumpMultiplier_denseRange.comp
    unitFourierCoreRestriction_denseRange
    unitFourierCoreBumpMultiplier.continuous

noncomputable def unitFourierCoreProduct
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
    unitFourierCoreBumpSchwartz f

@[simp] theorem unitFourierCoreProduct_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    unitFourierCoreProduct f x =
      unitFourierCoreBumpSchwartz x * f x := rfl

theorem unitFourierDenseCore_eq_restrict_product
    (f : SchwartzMap ℝ ℂ) :
    unitFourierDenseCore f =
      globalL2ToKernelInterval (-1) 1 0
        ((unitFourierCoreProduct f).toLp 2) := by
  rw [Lp.ext_iff]
  change (unitFourierCoreBumpMultiplier
      (unitFourierCoreRestriction f) : Jadd → ℂ) =ᵐ[volume] _
  have hcore := unitFourierCoreBumpMultiplier_coeFn
    (unitFourierCoreRestriction f)
  have hrestricted := globalL2ToKernelInterval_coeFn
    (-1) 1 0 ((unitFourierCoreProduct f).toLp 2)
  have hschwartz :=
    (measurePreserving_kernelIntervalSubtypeVal (-1) 1 0)
      |>.quasiMeasurePreserving.ae_eq
        (ae_restrict_of_ae (s := Set.Icc (-1 - 0 : ℝ) (1 + 0))
          ((unitFourierCoreProduct f).coeFn_toLp 2 volume))
  have hinput := globalL2ToKernelInterval_coeFn
    (-1) 1 0 (f.toLp 2)
  have hf :=
    (measurePreserving_kernelIntervalSubtypeVal (-1) 1 0)
      |>.quasiMeasurePreserving.ae_eq
        (ae_restrict_of_ae (s := Set.Icc (-1 - 0 : ℝ) (1 + 0))
          (f.coeFn_toLp 2 volume))
  filter_upwards [hcore, hrestricted, hschwartz, hinput, hf] with
      x hcoreAt hrestrictedAt hschwartzAt hinputAt hfAt
  rw [hcoreAt, hrestrictedAt]
  rw [unitFourierCoreRestriction, ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.toLpCLM_apply]
  rw [hinputAt]
  change (f.toLp 2 volume : ℝ → ℂ) x.1 = f x.1 at hfAt
  change ((unitFourierCoreProduct f).toLp 2 volume : ℝ → ℂ) x.1 =
    unitFourierCoreProduct f x.1 at hschwartzAt
  rw [hfAt, hschwartzAt]
  rfl

theorem unitFourierCoreProduct_support
    (f : SchwartzMap ℝ ℂ) :
    Function.support (unitFourierCoreProduct f) ⊆
      Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  have hbump : unitFourierCoreBumpSchwartz x ≠ 0 := by
    intro hzero
    apply hx
    rw [unitFourierCoreProduct_apply, hzero, zero_mul]
  have hxball : x ∈ Metric.ball (0 : ℝ) 1 := by
    have hbumpReal : unitFourierCoreBump x ≠ 0 := by
      intro hzero
      apply hbump
      rw [unitFourierCoreBumpSchwartz_apply, hzero]
      norm_num
    have hxSupport : x ∈ Function.support unitFourierCoreBump := hbumpReal
    have hxRaw : x ∈ Metric.ball (0 : ℝ) unitFourierCoreBump.rOut := by
      rw [← unitFourierCoreBump.support_eq]
      exact hxSupport
    simpa only [unitFourierCoreBump] using hxRaw
  rw [Metric.mem_ball, Real.dist_eq] at hxball
  simp only [sub_zero] at hxball
  exact ⟨(abs_lt.mp hxball).1.le, (abs_lt.mp hxball).2.le⟩

theorem unitFourierCoreProduct_zeroExtension
    (f : SchwartzMap ℝ ℂ) :
    kernelIntervalL2ZeroExtension (-1) 1 0
        (unitFourierDenseCore f) =
      kernelIntervalProjection (-1) 1 0
        ((unitFourierCoreProduct f).toLp 2) := by
  rw [unitFourierDenseCore_eq_restrict_product]
  unfold kernelIntervalProjection
  rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
  simp only [ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]

theorem unitFourierCoreProduct_projection
    (f : SchwartzMap ℝ ℂ) :
    kernelIntervalProjection (-1) 1 0
        ((unitFourierCoreProduct f).toLp 2) =
      (unitFourierCoreProduct f).toLp 2 := by
  apply Lp.ext_iff.mpr
  have hprojection := kernelIntervalProjection_coeFn
    (-1) 1 0 ((unitFourierCoreProduct f).toLp 2)
  have hproduct := (unitFourierCoreProduct f).coeFn_toLp 2 volume
  have hsupport := unitFourierCoreProduct_support f
  filter_upwards [hprojection, hproduct] with x hx hp
  rw [hx, hp]
  simp only [sub_zero, add_zero]
  by_cases hmem : x ∈ Set.Icc (-1 : ℝ) 1
  · simp only [Set.indicator_of_mem hmem]
    exact hp
  · have hzero : unitFourierCoreProduct f x = 0 := by
      by_contra hne
      exact hmem (hsupport hne)
    rw [hzero]
    simp only [Set.indicator_of_notMem hmem]

theorem unitAdditiveFourierKernel_coefficient_coreProduct
    (f : SchwartzMap ℝ ℂ) (y : Jadd) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure Jadd) unitAdditiveFourierKernel
        (globalL2ToKernelInterval (-1) 1 0
          ((unitFourierCoreProduct f).toLp 2)) y =
      𝓕 (unitFourierCoreProduct f) y.1 := by
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [unitAdditiveFourierKernel_coefficient_eq_fourierIntegral]
  change (∫ x : Jadd,
      (𝐞 (-(x.1 * y.1)) : ℂ) * unitFourierCoreProduct f x.1
        ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap (μ := (volume : Measure ℝ))
    measurableSet_Icc
    (fun x : ℝ => (𝐞 (-(x * y.1)) : ℂ) * unitFourierCoreProduct f x)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial, Circle.smul_def]
    rw [mul_comm x y.1]
    rfl
  · intro x hx
    have hproduct : unitFourierCoreProduct f x = 0 := by
      by_contra hne
      exact hx (by simpa only [sub_zero, add_zero] using
        unitFourierCoreProduct_support f hne)
    rw [hproduct, mul_zero]

theorem unitAdditiveIntervalFourierOperator_denseCore
    (f : SchwartzMap ℝ ℂ) :
    unitAdditiveIntervalFourierOperator (unitFourierDenseCore f) =
      globalL2ToKernelInterval (-1) 1 0
        (Lp.fourierTransformₗᵢ ℝ ℂ
          (kernelIntervalL2ZeroExtension (-1) 1 0
            (unitFourierDenseCore f))) := by
  have hzeroExtension :
      kernelIntervalL2ZeroExtension (-1) 1 0
          (unitFourierDenseCore f) =
        (unitFourierCoreProduct f).toLp 2 := by
    rw [unitFourierCoreProduct_zeroExtension,
      unitFourierCoreProduct_projection]
  have hfourierL2 :
      Lp.fourierTransformₗᵢ ℝ ℂ
          ((unitFourierCoreProduct f).toLp 2) =
        (𝓕 (unitFourierCoreProduct f)).toLp 2 := by
    exact SchwartzMap.toLp_fourier_eq (unitFourierCoreProduct f)
  rw [hzeroExtension, hfourierL2]
  rw [Lp.ext_iff]
  change (ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ
      (ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure Jadd) unitAdditiveFourierKernel
        (unitFourierDenseCore f)) : Jadd → ℂ) =ᵐ[volume] _
  have hleft := ContinuousMap.coeFn_toLp
    (p := 2) (𝕜 := ℂ) (volume : Measure Jadd)
    (ContinuousKernelHilbertSchmidt.coefficient
      (volume : Measure Jadd) unitAdditiveFourierKernel
      (unitFourierDenseCore f))
  have hright := globalL2ToKernelInterval_coeFn
    (-1) 1 0 ((𝓕 (unitFourierCoreProduct f)).toLp 2)
  have hfourier :=
    (measurePreserving_kernelIntervalSubtypeVal (-1) 1 0)
      |>.quasiMeasurePreserving.ae_eq
        (ae_restrict_of_ae (s := Set.Icc (-1 - 0 : ℝ) (1 + 0))
          ((𝓕 (unitFourierCoreProduct f)).coeFn_toLp 2 volume))
  filter_upwards [hleft, hright, hfourier] with y hleftAt hrightAt hfourierAt
  simp only [Function.comp_apply] at hfourierAt
  rw [hleftAt, hrightAt, hfourierAt]
  rw [unitFourierDenseCore_eq_restrict_product]
  exact unitAdditiveFourierKernel_coefficient_coreProduct f y

theorem unitAdditiveIntervalFourierOperator_eq_restrict_fourier_zeroExtension
    (u : Lp ℂ 2 (volume : Measure Jadd)) :
    unitAdditiveIntervalFourierOperator u =
      globalL2ToKernelInterval (-1) 1 0
        (Lp.fourierTransformₗᵢ ℝ ℂ
          (kernelIntervalL2ZeroExtension (-1) 1 0 u)) := by
  refine DenseRange.induction_on unitFourierDenseCore_denseRange u
    (isClosed_eq unitAdditiveIntervalFourierOperator.continuous
      (by fun_prop)) ?_
  intro f
  exact unitAdditiveIntervalFourierOperator_denseCore f

theorem unitKernelIntervalProjection_apply
    (u : cc20GlobalLogCrossingL2) :
    kernelIntervalProjection (-1) 1 0 u =
      kernelIntervalL2ZeroExtension (-1) 1 0
        (globalL2ToKernelInterval (-1) 1 0 u) := by
  have hadjoint :
      (kernelIntervalL2ZeroExtension (-1) 1 0).adjoint =
        globalL2ToKernelInterval (-1) 1 0 := by
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [kernelIntervalProjection, ContinuousLinearMap.comp_apply, hadjoint]

theorem unitAdditiveFiniteWindowFourierFactor_apply
    (u : cc20GlobalLogCrossingL2) :
    unitAdditiveFiniteWindowFourierFactor u =
      kernelIntervalProjection (-1) 1 0
        (Lp.fourierTransformₗᵢ ℝ ℂ
          (kernelIntervalProjection (-1) 1 0 u)) := by
  rw [unitKernelIntervalProjection_apply,
    unitKernelIntervalProjection_apply]
  unfold unitAdditiveFiniteWindowFourierFactor
  simp only [ContinuousLinearMap.comp_apply]
  rw [unitAdditiveIntervalFourierOperator_eq_restrict_fourier_zeroExtension]

theorem ccm24EvenSymmetrizationToEven_subtype
    (u : Hadd) :
    ccm24EvenSymmetrizationToEven
        (u : cc20GlobalLogCrossingL2) = u := by
  apply Subtype.ext
  change ccm24EvenSymmetrizationCLM
      (u : cc20GlobalLogCrossingL2) = u
  rw [ccm24EvenSymmetrizationCLM_apply]
  have hu :=
    (mem_ccm24EvenAdditiveClosedSubspace_iff
      (u : cc20GlobalLogCrossingL2)).1 u.property
  rw [hu, ← two_smul ℂ (u : cc20GlobalLogCrossingL2), ← mul_smul]
  norm_num

theorem unitEvenAdditiveFourierCompression_eq_finiteWindowFactor :
    unitEvenAdditiveFourierCompression =
      unitEvenAdditiveFiniteWindowFourierFactor := by
  apply ContinuousLinearMap.ext
  intro u
  rw [unitEvenAdditiveFourierCompression_eq_literalProjection]
  simp only [ContinuousLinearMap.comp_apply]
  let v : Hadd :=
    unitLiteralEvenAdditiveInteriorProjection
      (ccm24EvenAdditiveFourier
        (unitLiteralEvenAdditiveInteriorProjection u))
  have hfactor :
      unitAdditiveFiniteWindowFourierFactor
          (u : cc20GlobalLogCrossingL2) =
        (v : cc20GlobalLogCrossingL2) := by
    rw [unitAdditiveFiniteWindowFourierFactor_apply]
    rw [show (v : cc20GlobalLogCrossingL2) =
        kernelIntervalProjection (-1) 1 0
          ((ccm24EvenAdditiveFourier
            (unitLiteralEvenAdditiveInteriorProjection u) : Hadd) :
              cc20GlobalLogCrossingL2) by
      exact unitLiteralEvenAdditiveInteriorProjection_coe _]
    change kernelIntervalProjection (-1) 1 0
        (Lp.fourierTransformₗᵢ ℝ ℂ
          (kernelIntervalProjection (-1) 1 0
            (u : cc20GlobalLogCrossingL2))) =
      kernelIntervalProjection (-1) 1 0
        (Lp.fourierTransformₗᵢ ℝ ℂ
          ((unitLiteralEvenAdditiveInteriorProjection u : Hadd) :
            cc20GlobalLogCrossingL2))
    rw [unitLiteralEvenAdditiveInteriorProjection_coe]
  change v =
    ccm24EvenSymmetrizationToEven
      (unitAdditiveFiniteWindowFourierFactor
        (u : cc20GlobalLogCrossingL2))
  rw [hfactor, ccm24EvenSymmetrizationToEven_subtype]

/-- The raw unit-scale Hardy--Titchmarsh support crossing is genuinely
Hilbert--Schmidt.  The former operator-identification premise is discharged by
the Plancherel/kernel equality above. -/
theorem unitRawSupportCrossing_summable_of_additiveKernelIdentification
    {ι : Type*} (basis : HilbertBasis ι ℂ H) :
    Summable fun i => ‖unitRawSupportCrossing (basis i)‖ ^ 2 := by
  have hadditive : Summable fun i =>
      ‖unitEvenAdditiveFourierCompression
        (unitEvenAdditiveBasis basis i)‖ ^ 2 := by
    rw [unitEvenAdditiveFourierCompression_eq_finiteWindowFactor]
    exact unitEvenAdditiveFiniteWindowFourierFactor_summable
      (unitEvenAdditiveBasis basis)
  have hlog : Summable fun i =>
      ‖unitInteriorFourierCompression (basis i)‖ ^ 2 :=
    (unitInteriorFourierCompression_summable_iff_evenAdditive basis).2
      hadditive
  exact unitRawSupportCrossing_summable_of_interiorCompression basis hlog

end ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction
