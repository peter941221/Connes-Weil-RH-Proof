/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ProlateTraceReduction
import ConnesWeilRH.Source.CC20Concrete.CCM24GaussianMellin
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

/-!
# Unit-scale prolate trace reduction

This module applies the generic two-projection defect theorem to the literal
CC20 source cutoff.  It reduces the missing positive trace-class theorem to
two source-specific facts about one actual operator:

1. the raw Hardy--Titchmarsh half-line crossing is Hilbert--Schmidt;
2. the complementary support angle is strict.

Neither fact is assumed globally or packaged as stored spectral data.  They
remain explicit premises until constructed from the CC20 unit-scale source.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24UnitScaleProlateTraceReduction

open MeasureTheory
open scoped ComplexConjugate FourierTransform
open CC20Concrete
open CC20Concrete.ProlateTraceReduction
open CC20Concrete.PositiveTrace
open CC20Concrete.ContinuousKernelHilbertSchmidt
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace
open CCM24UnitScaleProlateAlignment
open SelectedCrossingKernel
open SelectedCrossingOperatorBridge

local notation "Hinf" => ccm24ArchimedeanHardyTitchmarsh
local notation "H" => finiteSCarrier
local notation "Hop" => archimedeanHardyTitchmarshOperator
local notation "Hadd" => ccm24EvenAdditiveL2
local notation "Elog" => ccm24EvenLogCarrierEquiv
local notation "Fadd" => ccm24EvenAdditiveFourier
local notation "Jadd" => KernelInterval (-1) 1 0

noncomputable local instance : CompleteSpace Hadd :=
  ccm24EvenAdditiveClosedSubspace.isClosed.completeSpace_coe

noncomputable abbrev unitProlateFactor : H →L[ℂ] H :=
  prolateFactor Hinf

noncomputable abbrev unitProlateDefectFactor : H →L[ℂ] H :=
  prolateDefectFactor Hinf

noncomputable abbrev unitRawSupportCrossing : H →L[ℂ] H :=
  (ContinuousLinearMap.id ℂ H - cc20PositiveHalfLineProjection) ∘L
    cc20TransportedHalfLineProjection Hinf ∘L
      cc20PositiveHalfLineProjection

/-- Projection onto the complementary finite physical window at unit scale. -/
noncomputable abbrev unitInteriorSupportProjection : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - cc20PositiveHalfLineProjection

/-- The finite-window compression of the genuine archimedean Fourier
involution. -/
noncomputable abbrev unitInteriorFourierCompression : H →L[ℂ] H :=
  unitInteriorSupportProjection ∘L Hop ∘L
    unitInteriorSupportProjection

/-- The unit interior projection read back on the genuine additive-even
carrier.  This is a definition by exact unitary transport, not an independent
support premise. -/
noncomputable def unitEvenAdditiveInteriorProjection : Hadd →L[ℂ] Hadd :=
  ccm24EvenLogCarrierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    unitInteriorSupportProjection ∘L
      ccm24EvenLogCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap

/-- The finite-window Fourier compression on the genuine additive-even
carrier.  The next analytic producer identifies the transported interior
projection with the literal additive interval `[-1,1]`. -/
noncomputable def unitEvenAdditiveFourierCompression : Hadd →L[ℂ] Hadd :=
  unitEvenAdditiveInteriorProjection ∘L
    ccm24EvenAdditiveFourier.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      unitEvenAdditiveInteriorProjection

/-- The literal compact Fourier kernel on the additive unit interval.  The
positive character is intentional: `coefficient` conjugates its first inner
product argument and therefore produces Mathlib's negative Fourier phase. -/
noncomputable def unitAdditiveFourierKernel :
    ContinuousMap (Jadd × Jadd) ℂ where
  toFun z := (𝐞 (z.2.1 * z.1.1) : ℂ)
  continuous_toFun := by fun_prop

/-- The genuine finite-window Fourier integral operator on `L²([-1,1])`. -/
noncomputable def unitAdditiveIntervalFourierOperator :
    Lp ℂ 2 (volume : Measure Jadd) →L[ℂ]
      Lp ℂ 2 (volume : Measure Jadd) :=
  ContinuousKernelHilbertSchmidt.operator
    (volume : Measure Jadd) (volume : Measure Jadd)
    unitAdditiveFourierKernel

/-- The kernel coefficient has exactly Mathlib's negative Fourier phase.
This checks both the inner-product conjugation and the `2π` normalization
before any Plancherel identification is attempted. -/
theorem unitAdditiveFourierKernel_coefficient_eq_fourierIntegral
    (f : ContinuousMap Jadd ℂ) (y : Jadd) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure Jadd) unitAdditiveFourierKernel
        (ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ f) y =
      ∫ x : Jadd, (𝐞 (-(x.1 * y.1)) : ℂ) * f x := by
  change inner ℂ
      (ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          unitAdditiveFourierKernel y))
      (ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ f) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards with x
  change f x * star (𝐞 (x.1 * y.1) : ℂ) =
    (𝐞 (-(x.1 * y.1)) : ℂ) * f x
  have hcharacter (r : ℝ) :
      star (𝐞 r : ℂ) = (𝐞 (-r) : ℂ) := by
    rw [AddChar.map_neg_eq_inv]
    exact (Circle.coe_inv_eq_conj (𝐞 r)).symm
  rw [hcharacter]
  exact mul_comm _ _

/-- Continuous compactness of the Fourier kernel gives its actual
Hilbert--Schmidt basis summability. -/
theorem unitAdditiveIntervalFourierOperator_summable
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure Jadd))) :
    Summable fun i =>
      ‖unitAdditiveIntervalFourierOperator (basis i)‖ ^ 2 := by
  exact ContinuousKernelHilbertSchmidt.basis_normSq_summable
    (volume : Measure Jadd) (volume : Measure Jadd)
    unitAdditiveFourierKernel basis

/-- Restrict to the additive unit interval, apply its genuine Fourier kernel,
and extend by zero. -/
noncomputable def unitAdditiveFiniteWindowFourierFactor :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  kernelIntervalL2ZeroExtension (-1) 1 0 ∘L
    unitAdditiveIntervalFourierOperator ∘L
      globalL2ToKernelInterval (-1) 1 0

/-- The literal whole-line finite-window Fourier factor is Hilbert--Schmidt
along every named whole-line Hilbert basis. -/
theorem unitAdditiveFiniteWindowFourierFactor_summable
    {ι : Type*}
    (basis : HilbertBasis ι ℂ cc20GlobalLogCrossingL2) :
    Summable fun i =>
      ‖unitAdditiveFiniteWindowFourierFactor (basis i)‖ ^ 2 := by
  obtain ⟨index, intervalBasis, _⟩ :=
    exists_hilbertBasis (𝕜 := ℂ)
      (E := Lp ℂ 2 (volume : Measure Jadd))
  have hkernel :=
    unitAdditiveIntervalFourierOperator_summable intervalBasis
  have hrestrict := summable_normSq_precomp
    intervalBasis intervalBasis basis
    unitAdditiveIntervalFourierOperator
    (globalL2ToKernelInterval (-1) 1 0) hkernel
  exact summable_normSq_postcomp basis
    (unitAdditiveIntervalFourierOperator ∘L
      globalL2ToKernelInterval (-1) 1 0)
    (kernelIntervalL2ZeroExtension (-1) 1 0) hrestrict

/-- The same literal finite-window factor, restricted to the even additive
carrier.  Even symmetrization on the output is bounded and does not affect
Hilbert--Schmidt summability. -/
noncomputable def unitEvenAdditiveFiniteWindowFourierFactor :
    Hadd →L[ℂ] Hadd :=
  ccm24EvenSymmetrizationToEven ∘L
    unitAdditiveFiniteWindowFourierFactor ∘L
      ccm24EvenAdditiveClosedSubspace.subtypeL

theorem unitEvenAdditiveFiniteWindowFourierFactor_summable
    {ι : Type*} (basis : HilbertBasis ι ℂ Hadd) :
    Summable fun i =>
      ‖unitEvenAdditiveFiniteWindowFourierFactor (basis i)‖ ^ 2 := by
  obtain ⟨index, globalBasis, _⟩ :=
    exists_hilbertBasis (𝕜 := ℂ) (E := cc20GlobalLogCrossingL2)
  have hglobal :=
    unitAdditiveFiniteWindowFourierFactor_summable globalBasis
  have hrestrict := summable_normSq_precomp
    globalBasis globalBasis basis
    unitAdditiveFiniteWindowFourierFactor
    ccm24EvenAdditiveClosedSubspace.subtypeL hglobal
  exact summable_normSq_postcomp basis
    (unitAdditiveFiniteWindowFourierFactor ∘L
      ccm24EvenAdditiveClosedSubspace.subtypeL)
    ccm24EvenSymmetrizationToEven hrestrict

/-- The literal additive unit-interval projection preserves the even closed
subspace.  Symmetry is proved on representatives; no abstract range premise
is introduced. -/
theorem unitAdditiveIntervalProjection_mem_even (u : Hadd) :
    kernelIntervalProjection (-1) 1 0
        (u : cc20GlobalLogCrossingL2) ∈
      ccm24EvenAdditiveClosedSubspace := by
  rw [mem_ccm24EvenAdditiveClosedSubspace_iff_ae_even]
  have hprojection := kernelIntervalProjection_coeFn
    (-1) 1 0 (u : cc20GlobalLogCrossingL2)
  have hprojectionNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      hprojection
  have heven := ccm24EvenAdditiveRepresentative_ae_even u
  have hrepresentative := ccm24EvenAdditiveRepresentative_ae_eq u
  have hrepresentativeNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      hrepresentative
  filter_upwards
    [hprojection, hprojectionNeg, heven,
      hrepresentative, hrepresentativeNeg] with
      x hprojectionAt hprojectionNegAt hevenAt
      hrepresentativeAt hrepresentativeNegAt
  simp only [Function.comp_apply] at hprojectionNegAt hrepresentativeNegAt
  rw [hprojectionNegAt, hprojectionAt]
  simp only [sub_zero, add_zero]
  have hmemNeg :
      -x ∈ Set.Icc (-1 : ℝ) 1 ↔ x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> intro hx
    · constructor <;> linarith [hx.1, hx.2]
    · constructor <;> linarith [hx.1, hx.2]
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem (hmemNeg.mpr hx)]
    rw [hrepresentativeNegAt, hrepresentativeAt, hevenAt]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx (hmemNeg.mp h))]

/-- Literal restriction to `[-1,1]` as an endomorphism of the genuine
additive-even carrier. -/
noncomputable def unitLiteralEvenAdditiveInteriorProjection :
    Hadd →L[ℂ] Hadd :=
  (kernelIntervalProjection (-1) 1 0 ∘L
      ccm24EvenAdditiveClosedSubspace.subtypeL).codRestrict
    ccm24EvenAdditiveClosedSubspace.toSubmodule
    unitAdditiveIntervalProjection_mem_even

theorem unitLiteralEvenAdditiveInteriorProjection_coe
    (u : Hadd) :
    ((unitLiteralEvenAdditiveInteriorProjection u : Hadd) :
        cc20GlobalLogCrossingL2) =
      kernelIntervalProjection (-1) 1 0
        (u : cc20GlobalLogCrossingL2) :=
  rfl

/-- The transported common-log interior projection is exactly the literal
additive cutoff `[-1,1]`.  The only endpoint discrepancy is at `t=0`, a
Lebesgue-null set. -/
theorem unitEvenAdditiveInteriorProjection_eq_literal :
    unitEvenAdditiveInteriorProjection =
      unitLiteralEvenAdditiveInteriorProjection := by
  apply ContinuousLinearMap.ext
  intro u
  apply ccm24EvenLogCarrierEquiv.injective
  unfold unitEvenAdditiveInteriorProjection
  simp only [ContinuousLinearMap.comp_apply]
  change ccm24EvenLogCarrierEquiv
      (ccm24EvenLogCarrierEquiv.symm
        (unitInteriorSupportProjection (ccm24EvenLogCarrierEquiv u))) =
    ccm24EvenLogCarrierEquiv
      (unitLiteralEvenAdditiveInteriorProjection u)
  rw [ccm24EvenLogCarrierEquiv.apply_symm_apply]
  rw [Lp.ext_iff]
  let v : Hadd := unitLiteralEvenAdditiveInteriorProjection u
  have hleft :
      (unitInteriorSupportProjection (ccm24EvenLogCarrierEquiv u) :
          ℝ → ℂ) =ᵐ[volume]
        (Set.Iio 0).indicator
          (fun t => (ccm24EvenLogCarrierEquiv u : ℝ → ℂ) t) := by
    exact cc20NegativeHalfLineProjection_coeFn
      (ccm24EvenLogCarrierEquiv u)
  have hforward :
      (ccm24EvenLogCarrierEquiv v : ℝ → ℂ) =ᵐ[volume]
        ccm24NormalizedLogHalfDensityRaw v :=
    ccm24EvenToLogHalfDensity_coeFn v
  have hforwardU :
      (ccm24EvenLogCarrierEquiv u : ℝ → ℂ) =ᵐ[volume]
        ccm24NormalizedLogHalfDensityRaw u :=
    ccm24EvenToLogHalfDensity_coeFn u
  have hliteral :
      (((v : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) =ᵐ[volume]
        (Set.Icc (-1 : ℝ) 1).indicator
          (fun x => ((u : Hadd) : cc20GlobalLogCrossingL2) x) := by
    have hprojection := kernelIntervalProjection_coeFn
      (-1) 1 0 ((u : Hadd) : cc20GlobalLogCrossingL2)
    simpa only [v, unitLiteralEvenAdditiveInteriorProjection_coe,
      sub_zero, add_zero] using hprojection
  have hrepV := ccm24EvenAdditiveRepresentative_ae_eq v
  have hrepU := ccm24EvenAdditiveRepresentative_ae_eq u
  have hsource :
      ccm24EvenAdditiveRepresentative v =ᵐ[volume]
        (Set.Icc (-1 : ℝ) 1).indicator
          (ccm24EvenAdditiveRepresentative u) := by
    filter_upwards [hrepV, hliteral, hrepU] with x hv hl hu
    calc
      ccm24EvenAdditiveRepresentative v x =
          (((v : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) x := hv.symm
      _ = (Set.Icc (-1 : ℝ) 1).indicator
          (fun y => ((u : Hadd) : cc20GlobalLogCrossingL2) y) x := hl
      _ = (Set.Icc (-1 : ℝ) 1).indicator
          (ccm24EvenAdditiveRepresentative u) x := by
        by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
        · simp only [Set.indicator_of_mem hx]
          exact hu
        · simp only [Set.indicator_of_notMem hx]
  have htransport := ccm24NormalizedLogHalfDensityFunction_congr_ae
    (stronglyMeasurable_ccm24EvenAdditiveRepresentative v)
    ((stronglyMeasurable_ccm24EvenAdditiveRepresentative u).indicator
      measurableSet_Icc)
    hsource
  have hpoint (t : ℝ) (ht0 : t ≠ 0) :
      ccm24NormalizedLogHalfDensityFunction
          ((Set.Icc (-1 : ℝ) 1).indicator
            (ccm24EvenAdditiveRepresentative u)) t =
        (Set.Iio 0).indicator
          (ccm24NormalizedLogHalfDensityRaw u) t := by
    unfold ccm24NormalizedLogHalfDensityRaw
      ccm24NormalizedLogHalfDensityFunction
    by_cases ht : t < 0
    · have hexp : Real.exp t ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor
        · linarith [Real.exp_pos t]
        · exact (Real.exp_lt_one_iff.mpr ht).le
      have htmem : t ∈ Set.Iio (0 : ℝ) := ht
      rw [Set.indicator_of_mem hexp, Set.indicator_of_mem htmem]
    · have htpos : 0 < t :=
        lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm ht0)
      have hexp : Real.exp t ∉ Set.Icc (-1 : ℝ) 1 := by
        intro hmem
        exact (not_le_of_gt (Real.one_lt_exp_iff.mpr htpos)) hmem.2
      have hnotIio : t ∉ Set.Iio (0 : ℝ) := ht
      rw [Set.indicator_of_notMem hexp,
        Set.indicator_of_notMem hnotIio]
      simp only [smul_zero]
  filter_upwards
    [hleft, hforward, hforwardU, htransport,
      MeasureTheory.volume.ae_ne (0 : ℝ)] with
      t hleftAt hforwardAt hforwardUAt htransportAt ht0
  rw [hleftAt, hforwardAt]
  calc
    (Set.Iio 0).indicator
        (fun s => (ccm24EvenLogCarrierEquiv u : ℝ → ℂ) s) t =
        (Set.Iio 0).indicator
          (ccm24NormalizedLogHalfDensityRaw u) t := by
      by_cases ht : t ∈ Set.Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
          hforwardUAt]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
    _ = ccm24NormalizedLogHalfDensityFunction
        ((Set.Icc (-1 : ℝ) 1).indicator
          (ccm24EvenAdditiveRepresentative u)) t :=
      (hpoint t ht0).symm
    _ = ccm24NormalizedLogHalfDensityRaw v t := by
      simpa only [ccm24NormalizedLogHalfDensityRaw] using htransportAt.symm

/-- After the support identification, the additive compression uses the
literal unit-interval projection on both sides of the genuine Plancherel
Fourier involution. -/
theorem unitEvenAdditiveFourierCompression_eq_literalProjection :
    unitEvenAdditiveFourierCompression =
      unitLiteralEvenAdditiveInteriorProjection ∘L
        ccm24EvenAdditiveFourier.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          unitLiteralEvenAdditiveInteriorProjection := by
  unfold unitEvenAdditiveFourierCompression
  rw [unitEvenAdditiveInteriorProjection_eq_literal]

/-- A Hilbert basis transported from common-log coordinates to the genuine
additive-even carrier. -/
noncomputable def unitEvenAdditiveBasis
    {ι : Type*} (basis : HilbertBasis ι ℂ H) :
    HilbertBasis ι ℂ Hadd :=
  HilbertBasis.ofRepr (ccm24EvenLogCarrierEquiv.trans basis.repr)

@[simp] theorem unitEvenAdditiveBasis_apply
    {ι : Type*} (basis : HilbertBasis ι ℂ H) (i : ι) :
    unitEvenAdditiveBasis basis i =
      ccm24EvenLogCarrierEquiv.symm (basis i) :=
  rfl

theorem unitProlateFactor_eq_source :
    unitProlateFactor =
      sourceProlateHilbertSchmidtFactor unitSoninScale := by
  unfold unitProlateFactor prolateFactor supportComplementProjection
    sourceProlateHilbertSchmidtFactor
  rw [radialSupportProjection_unit,
    sourceFourierSupportProjection_unit,
    sourceSoninProjection_unit]

theorem unitProlateDefectFactor_eq_rawSupportCrossing :
    unitProlateDefectFactor = unitRawSupportCrossing :=
  prolateDefectFactor_eq_rawSupportCrossing Hinf

theorem unitTransportedHalfLineProjection_eq_hardyConjugation :
    cc20TransportedHalfLineProjection Hinf =
      Hop ∘L cc20PositiveHalfLineProjection ∘L Hop := by
  apply ContinuousLinearMap.ext
  intro u
  rw [cc20TransportedHalfLineProjection_apply]
  rw [ccm24ArchimedeanHardyTitchmarsh_symm_apply]
  rfl

theorem archimedeanHardyTitchmarshOperator_eq_sourceFourier :
    Hop =
      ccm24ArchimedeanSourceFourier.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  exact (DFunLike.congr_fun
    ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh u).symm

/-- Exact carrier alignment for the finite-window Fourier compression.  No
estimate is used: both support cutoffs and the Fourier involution are moved
through the actual CCM24 unitary. -/
theorem unitInteriorFourierCompression_eq_evenAdditiveConjugation :
    unitInteriorFourierCompression =
      ccm24EvenLogCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        unitEvenAdditiveFourierCompression ∘L
          ccm24EvenLogCarrierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [unitInteriorFourierCompression,
    unitEvenAdditiveFourierCompression,
    unitEvenAdditiveInteriorProjection,
    ContinuousLinearMap.comp_apply]
  rw [archimedeanHardyTitchmarshOperator_eq_sourceFourier]
  change unitInteriorSupportProjection
      (Elog (Fadd (ccm24EvenLogCarrierEquiv.symm
        (unitInteriorSupportProjection u)))) = _
  simp

/-- Hilbert--Schmidt summability is invariant under the exact additive/log
unitary carrier change.  This theorem turns the remaining producer into a
statement solely about the genuine additive-even finite-window operator. -/
theorem unitInteriorFourierCompression_summable_iff_evenAdditive
    {ι : Type*} (basis : HilbertBasis ι ℂ H) :
    (Summable fun i =>
        ‖unitInteriorFourierCompression (basis i)‖ ^ 2) ↔
      Summable fun i =>
        ‖unitEvenAdditiveFourierCompression
          (unitEvenAdditiveBasis basis i)‖ ^ 2 := by
  apply summable_congr
  intro i
  rw [unitInteriorFourierCompression_eq_evenAdditiveConjugation]
  simp only [ContinuousLinearMap.comp_apply, unitEvenAdditiveBasis_apply]
  exact congrArg (fun r : ℝ => r ^ 2)
    (ccm24EvenLogCarrierEquiv.norm_map
      (unitEvenAdditiveFourierCompression
        (ccm24EvenLogCarrierEquiv.symm (basis i))))

/-- The raw unit-scale support crossing factors through the finite-window
Fourier compression.  The minus sign is the exact consequence of writing
`P = I - (I-P)` and using `H^2=I`. -/
theorem unitRawSupportCrossing_eq_neg_interiorCompression :
    unitRawSupportCrossing =
      -(unitInteriorFourierCompression ∘L Hop ∘L
        cc20PositiveHalfLineProjection) := by
  let P := cc20PositiveHalfLineProjection
  let I := unitInteriorSupportProjection
  apply ContinuousLinearMap.ext
  intro u
  unfold unitRawSupportCrossing
  rw [unitTransportedHalfLineProjection_eq_hardyConjugation]
  change I (Hop (P (Hop (P u)))) =
    -(I (Hop (I (Hop (P u)))))
  have hHinvolutive (v : H) : Hop (Hop v) = v :=
    archimedeanHardyTitchmarshOperator_involutive v
  have hPidempotent (v : H) : P (P v) = P v := by
    exact cc20PositiveHalfLineProjection_idempotent v
  dsimp only [I, unitInteriorSupportProjection]
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hHinvolutive, hPidempotent]
  abel

/-- Hilbert--Schmidt summability of the finite-window Fourier compression
implies the raw crossing summability required by the prolate trace reduction.
The transfer uses only bounded precomposition by `H P`. -/
theorem unitRawSupportCrossing_summable_of_interiorCompression
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (hcompression : Summable fun i =>
      ‖unitInteriorFourierCompression (basis i)‖ ^ 2) :
    Summable fun i => ‖unitRawSupportCrossing (basis i)‖ ^ 2 := by
  have hpre := summable_normSq_precomp basis basis basis
    unitInteriorFourierCompression
    (Hop ∘L cc20PositiveHalfLineProjection) hcompression
  rw [unitRawSupportCrossing_eq_neg_interiorCompression]
  simpa only [ContinuousLinearMap.neg_apply, norm_neg] using hpre

/-- Once the genuine Plancherel compression is identified with the already
constructed continuous-kernel factor, the raw Hardy--Titchmarsh crossing is
Hilbert--Schmidt.  This leaves one exact operator equality, not a spectral or
summability premise. -/
theorem unitRawSupportCrossing_summable_of_additiveKernelIdentification
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (hidentify : unitEvenAdditiveFourierCompression =
      unitEvenAdditiveFiniteWindowFourierFactor) :
    Summable fun i => ‖unitRawSupportCrossing (basis i)‖ ^ 2 := by
  have hadditive : Summable fun i =>
      ‖unitEvenAdditiveFourierCompression
        (unitEvenAdditiveBasis basis i)‖ ^ 2 := by
    rw [hidentify]
    exact unitEvenAdditiveFiniteWindowFourierFactor_summable
      (unitEvenAdditiveBasis basis)
  have hlog : Summable fun i =>
      ‖unitInteriorFourierCompression (basis i)‖ ^ 2 :=
    (unitInteriorFourierCompression_summable_iff_evenAdditive basis).2
      hadditive
  exact unitRawSupportCrossing_summable_of_interiorCompression basis hlog

/-- The exact unit-scale positive trace-class producer once the two genuine
CC20 analytic facts are supplied.  This theorem adds no spectral premise to
the project state: both obligations remain visible at the call site. -/
theorem sourceProlateRemainder_unit_isTraceClassAlong_of_rawCrossing
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (hangle : ‖unitProlateFactor‖ < 1)
    (hcrossing : Summable fun i =>
      ‖unitRawSupportCrossing (basis i)‖ ^ 2) :
    IsTraceClassAlong basis
      (sourceProlateRemainder unitSoninScale) := by
  have hdefect : Summable fun i =>
      ‖unitProlateDefectFactor (basis i)‖ ^ 2 := by
    simpa only [unitProlateDefectFactor_eq_rawSupportCrossing] using hcrossing
  rw [sourceProlateRemainder_unit]
  exact prolateRemainder_isTraceClassAlong_of_strictAngle basis Hinf
    hangle hdefect

/-- The same reduction in the Hilbert--Schmidt factor shape consumed by the
fixed-source three-branch ledger. -/
theorem sourceProlateHilbertSchmidtFactor_unit_summable_of_rawCrossing
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (hangle : ‖unitProlateFactor‖ < 1)
    (hcrossing : Summable fun i =>
      ‖unitRawSupportCrossing (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor unitSoninScale (basis i)‖ ^ 2 := by
  rw [← unitProlateFactor_eq_source]
  exact prolateFactor_summable_of_strictAngle basis Hinf hangle
    (by simpa only [unitProlateDefectFactor_eq_rawSupportCrossing] using
      hcrossing)

end CCM24UnitScaleProlateTraceReduction
end CCM25Concrete
end Source
end ConnesWeilRH
