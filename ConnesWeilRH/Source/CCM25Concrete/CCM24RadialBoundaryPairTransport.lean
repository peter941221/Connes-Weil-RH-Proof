/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24RadialHalfLineAlignment
import ConnesWeilRH.Source.CC20Concrete.CompactConvolutionSupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse

/-!
# Transport the compact half-line pair to the CCM24 radial boundary

The selected convolution detector commutes with logarithmic translations.
Consequently its commutator and oriented crossing at `log lambda` are unitary
translates of the fixed zero-boundary operators.  The compact-root
Hilbert--Schmidt pair is transported by the same bounded sandwich.

The fixed compact pair product is identified with the genuine positive
convolution crossing before translation, so the transported pair is an exact
trace-class owner of the radial boundary crossing.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24RadialBoundaryPairTransport

open MeasureTheory
open scoped ENNReal FourierTransform
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.CompactConvolutionSupport
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open SelectedCrossingOperatorBridge

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The archimedean Hardy--Titchmarsh unitary as an operator on the common
logarithmic carrier. -/
noncomputable def archimedeanHardyTitchmarshOperator : Op :=
  ccm24ArchimedeanHardyTitchmarsh.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def archimedeanScatteringMultiplierOperator : Op :=
  ccm24ArchimedeanScatteringMultiplier.toContinuousLinearEquiv
    |>.toContinuousLinearMap

noncomputable def logSpectralReflectionOperator : Op :=
  ccm24LogSpectralReflection.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def globalLogFourierOperator : Op :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearIsometry.toContinuousLinearMap

noncomputable def globalLogFourierInverseOperator : Op :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.toContinuousLinearMap

set_option maxHeartbeats 800000 in
-- Unfolding both `Lp` multipliers creates a large pointwise coercion goal.
/-- The archimedean phase multiplier commutes with every Schwartz Fourier
multiplier. -/
theorem archimedeanScatteringMultiplier_comp_fourierMultiplier
    (h : SchwartzMap ℝ ℂ) :
    archimedeanScatteringMultiplierOperator ∘L cc20FourierMultiplier h =
      cc20FourierMultiplier h ∘L archimedeanScatteringMultiplierOperator := by
  apply ContinuousLinearMap.ext
  intro u
  unfold archimedeanScatteringMultiplierOperator
  simp only [ContinuousLinearMap.comp_apply, cc20FourierMultiplier_apply]
  rw [Lp.ext_iff]
  filter_upwards
    [ccm24ArchimedeanScatteringMultiplier_coeFn ((𝓕 h).toLp ⊤ • u),
     Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      ((𝓕 h).toLp ⊤) u,
     Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      ((𝓕 h).toLp ⊤) (ccm24ArchimedeanScatteringMultiplier u),
     ccm24ArchimedeanScatteringMultiplier_coeFn u] with
      xi hleft hh hright hphase
  simp only [Pi.smul_apply'] at hh hright
  change ((ccm24ArchimedeanScatteringMultiplier
      ((𝓕 h).toLp ⊤ • u) : cc20GlobalLogCrossingL2) : ℝ → ℂ) xi =
    ((((𝓕 h).toLp ⊤) •
      ccm24ArchimedeanScatteringMultiplier u :
        cc20GlobalLogCrossingL2) : ℝ → ℂ) xi
  rw [hleft, hh, hright, hphase]
  simp only [smul_eq_mul]
  ring

/-- The selected detector with its spectral multiplier reflected through
`xi -> -xi`. -/
noncomputable def reflectedSpectralDetector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Op :=
  globalLogFourierInverseOperator ∘L logSpectralReflectionOperator ∘L
    cc20FourierMultiplier owner.sourceTest.convolutionSquare.test ∘L
      logSpectralReflectionOperator ∘L globalLogFourierOperator

theorem archimedeanHardyTitchmarshOperator_isSelfAdjoint :
    IsSelfAdjoint archimedeanHardyTitchmarshOperator := by
  apply ContinuousLinearMap.ext
  intro u
  unfold archimedeanHardyTitchmarshOperator
  exact ccm24ArchimedeanHardyTitchmarsh_adjoint_apply u

theorem archimedeanHardyTitchmarshOperator_involutive
    (u : finiteSCarrier) :
    archimedeanHardyTitchmarshOperator
        (archimedeanHardyTitchmarshOperator u) = u := by
  exact ccm24ArchimedeanHardyTitchmarsh_involutive u

/-- The repository's source second-support projection is the genuine
Hardy--Titchmarsh conjugate of the radial projection. -/
theorem sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation
    (lambda : CCM24SoninScale) :
    sourceFourierSupportProjection lambda =
      archimedeanHardyTitchmarshOperator ∘L
        radialSupportProjection lambda ∘L
          archimedeanHardyTitchmarshOperator := by
  rw [sourceFourierSupportProjection,
    ccm24ArchimedeanFourierSupportProjection_eq_transport]
  unfold ccm24ArchimedeanFourierSupportTransportProjection
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  rw [ccm24ArchimedeanHardyTitchmarsh_adjoint_apply]
  rfl

/-- Detector conjugated by the actual archimedean scattering involution. -/
noncomputable def hardyTitchmarshConjugatedDetector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Op :=
  archimedeanHardyTitchmarshOperator ∘L detectorOperator owner ∘L
    archimedeanHardyTitchmarshOperator

/-- The selected convolution root after the archimedean scattering
involution. -/
noncomputable def hardyTitchmarshConjugatedRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Op :=
  cc20GlobalLogConvolution owner.sourceTest.involution.test ∘L
    archimedeanHardyTitchmarshOperator

/-- The scattering-transformed detector remains the positive square of the
same selected convolution root followed by the actual Hardy--Titchmarsh
unitary. -/
theorem hardyTitchmarshConjugatedDetector_eq_adjoint_comp_root
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    hardyTitchmarshConjugatedDetector owner =
      (hardyTitchmarshConjugatedRoot owner).adjoint ∘L
        hardyTitchmarshConjugatedRoot owner := by
  unfold hardyTitchmarshConjugatedDetector
    hardyTitchmarshConjugatedRoot detectorOperator
    cc20GlobalConvolutionPositive
  rw [ContinuousLinearMap.adjoint_comp,
    archimedeanHardyTitchmarshOperator_isSelfAdjoint.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem hardyTitchmarshConjugatedDetector_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    IsSelfAdjoint (hardyTitchmarshConjugatedDetector owner) := by
  rw [hardyTitchmarshConjugatedDetector_eq_adjoint_comp_root]
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self
    (hardyTitchmarshConjugatedRoot owner)).isSelfAdjoint

/-- Conjugating the selected detector by the archimedean
Hardy--Titchmarsh involution only reflects its Fourier multiplier.  The
scattering phases cancel exactly. -/
theorem hardyTitchmarshConjugatedDetector_eq_reflectedSpectralDetector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    hardyTitchmarshConjugatedDetector owner =
      reflectedSpectralDetector owner := by
  apply ContinuousLinearMap.ext
  intro u
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  unfold hardyTitchmarshConjugatedDetector
    archimedeanHardyTitchmarshOperator reflectedSpectralDetector
    globalLogFourierOperator globalLogFourierInverseOperator
    logSpectralReflectionOperator detectorOperator
  simp only [ContinuousLinearMap.comp_apply]
  rw [globalConvolutionPositive_eq_convolutionSquare]
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
      (ccm24ArchimedeanHardyTitchmarsh
        (cc20GlobalLogConvolution owner.sourceTest.convolutionSquare.test
          (ccm24ArchimedeanHardyTitchmarsh u))) =
    (Lp.fourierTransformₗᵢ ℝ ℂ)
      ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (ccm24LogSpectralReflection
          (cc20FourierMultiplier owner.sourceTest.convolutionSquare.test
            (ccm24LogSpectralReflection
              ((Lp.fourierTransformₗᵢ ℝ ℂ) u)))))
  rw [ccm24ArchimedeanHardyTitchmarsh_fourier_readback]
  rw [fourier_globalLogConvolution]
  rw [ccm24ArchimedeanHardyTitchmarsh_fourier_readback]
  rw [(Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply]
  let z := (Lp.fourierTransformₗᵢ ℝ ℂ) u
  let A := cc20FourierMultiplier owner.sourceTest.convolutionSquare.test
  have hcommAt := congrArg
    (fun T : Op => T (ccm24LogSpectralReflection z))
    (archimedeanScatteringMultiplier_comp_fourierMultiplier
      owner.sourceTest.convolutionSquare.test)
  simp only [ContinuousLinearMap.comp_apply] at hcommAt
  change ccm24ArchimedeanScatteringMultiplier
      (A (ccm24LogSpectralReflection z)) =
    A (ccm24ArchimedeanScatteringMultiplier
      (ccm24LogSpectralReflection z)) at hcommAt
  change ccm24ArchimedeanScatteringMultiplier
      (ccm24LogSpectralReflection
        (A (ccm24ArchimedeanScatteringMultiplier
          (ccm24LogSpectralReflection z)))) =
    ccm24LogSpectralReflection (A (ccm24LogSpectralReflection z))
  rw [← hcommAt]
  have hinvolutive := ccm24ArchimedeanSpectralScattering_involutive
    (ccm24LogSpectralReflection (A (ccm24LogSpectralReflection z)))
  have hreflect : ccm24LogSpectralReflection
        (ccm24LogSpectralReflection
          (A (ccm24LogSpectralReflection z))) =
      A (ccm24LogSpectralReflection z) := by
    change ccm24LogSpectralReflectionLinearIsometry
        (ccm24LogSpectralReflectionLinearIsometry
          (A (ccm24LogSpectralReflection z))) =
      A (ccm24LogSpectralReflection z)
    exact ccm24LogSpectralReflection_involutive _
  rw [hreflect] at hinvolutive
  exact hinvolutive

/-- The genuine source second-support crossing is the Hardy--Titchmarsh
conjugate of a radial crossing for the scattering-transformed detector.  No
unsupported commutation of the selected detector with scattering is used. -/
theorem sourceSecondSupportOrientedCrossing_eq_hardyTitchmarsh_conjugation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    cc20OrientedBoundaryCrossing (sourceFourierSupportProjection lambda)
        (detectorOperator owner) =
      archimedeanHardyTitchmarshOperator ∘L
        cc20OrientedBoundaryCrossing (radialSupportProjection lambda)
          (hardyTitchmarshConjugatedDetector owner) ∘L
        archimedeanHardyTitchmarshOperator := by
  rw [sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation]
  apply ContinuousLinearMap.ext
  intro u
  unfold cc20OrientedBoundaryCrossing hardyTitchmarshConjugatedDetector
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [map_sub]
  rw [archimedeanHardyTitchmarshOperator_involutive]

/-- The complete source second-support commutator is the corresponding
Hardy--Titchmarsh conjugate of the radial commutator for the transformed
detector. -/
theorem sourceSecondSupportCommutator_eq_hardyTitchmarsh_conjugation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    cc20Commutator (sourceFourierSupportProjection lambda)
        (detectorOperator owner) =
      archimedeanHardyTitchmarshOperator ∘L
        cc20Commutator (radialSupportProjection lambda)
          (hardyTitchmarshConjugatedDetector owner) ∘L
        archimedeanHardyTitchmarshOperator := by
  rw [cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (sourceFourierSupportProjection lambda) (detectorOperator owner)
    (sourceFourierSupportProjection_isStarProjection lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)]
  rw [cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (radialSupportProjection lambda)
    (hardyTitchmarshConjugatedDetector owner)
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint
    (hardyTitchmarshConjugatedDetector_isSelfAdjoint owner)]
  rw [sourceSecondSupportOrientedCrossing_eq_hardyTitchmarsh_conjugation]
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    archimedeanHardyTitchmarshOperator_isSelfAdjoint.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]

/-- The project-level radial projection is the translated ordinary
half-line projection. -/
theorem radialSupportProjection_eq_translation_conjugation
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda =
      (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap ∘L
        cc20PositiveHalfLineProjection ∘L
          (cc20GlobalLogTranslation
            (Real.log lambda)).toContinuousLinearMap := by
  change ccm24LogRadialSupportProjection lambda = _
  exact ccm24LogRadialSupportProjection_eq_translation_conjugation lambda

/-- The actual selected detector commutator at the radial cutoff is the
translated fixed half-line commutator. -/
theorem detectorRadialCommutator_eq_translation_conjugation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    detectorOperator owner ∘L radialSupportProjection lambda -
        radialSupportProjection lambda ∘L detectorOperator owner =
      (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap ∘L
        (detectorOperator owner ∘L cc20PositiveHalfLineProjection -
          cc20PositiveHalfLineProjection ∘L detectorOperator owner) ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
  change detectorOperator owner ∘L
      ccm24LogRadialSupportProjection lambda -
        ccm24LogRadialSupportProjection lambda ∘L detectorOperator owner = _
  exact ccm24RadialCommutator_eq_translation_conjugation
    lambda (detectorOperator owner)
      (detectorOperator_comp_translation owner (Real.log lambda))
      (detectorOperator_comp_translation owner (-Real.log lambda))

/-- The selected oriented outer crossing reduces to the zero-boundary
crossing before any trace or norm is taken. -/
theorem detectorRadialOrientedCrossing_eq_translation_conjugation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (ContinuousLinearMap.id ℂ finiteSCarrier -
        radialSupportProjection lambda) ∘L detectorOperator owner ∘L
        radialSupportProjection lambda =
      (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap ∘L
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
            cc20PositiveHalfLineProjection) ∘L detectorOperator owner ∘L
          cc20PositiveHalfLineProjection) ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
  change (ContinuousLinearMap.id ℂ finiteSCarrier -
      ccm24LogRadialSupportProjection lambda) ∘L
        detectorOperator owner ∘L
      ccm24LogRadialSupportProjection lambda = _
  exact ccm24RadialOrientedCrossing_eq_translation_conjugation
    lambda (detectorOperator owner)
      (detectorOperator_comp_translation owner (-Real.log lambda))

/-- Transport the actual compact-root pair to the CCM24 radial cutoff. -/
noncomputable def translatedCompactRootPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))
      globalBasis :=
  (pairData owner.sourceTest a c negativeBasis positiveBasis outputBasis
    globalBasis).boundedSandwich outputBasis
      (cc20GlobalLogTranslation
        (-Real.log lambda)).toContinuousLinearMap
      (cc20GlobalLogTranslation
        (Real.log lambda)).toContinuousLinearMap

theorem translatedCompactRootPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct =
      (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap ∘L
        (pairData owner.sourceTest a c negativeBasis positiveBasis
          outputBasis globalBasis).traceProduct ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
  unfold translatedCompactRootPairData
  exact CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq
      outputBasis
      (pairData owner.sourceTest a c negativeBasis positiveBasis outputBasis
        globalBasis)
      (cc20GlobalLogTranslation
        (-Real.log lambda)).toContinuousLinearMap
      (cc20GlobalLogTranslation
        (Real.log lambda)).toContinuousLinearMap

theorem translatedCompactRootPairData_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).traceProduct :=
  (translatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis).traceProduct_isTraceClassAlong

/-- Unitary radial translation does not change the legal compact-pair trace.
The proof cycles both pair owners onto their common compact output carrier,
where the inverse translations cancel before any infinite-dimensional trace
cycle is attempted. -/
theorem ordinaryTraceAlong_translatedCompactRootPairData_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (translatedCompactRootPairData owner lambda a c negativeBasis
          positiveBasis outputBasis globalBasis).traceProduct =
      PositiveTrace.ordinaryTraceAlong globalBasis
        (pairData owner.sourceTest a c negativeBasis positiveBasis
          outputBasis globalBasis).traceProduct := by
  let original := pairData owner.sourceTest a c negativeBasis positiveBasis
    outputBasis globalBasis
  let translated := translatedCompactRootPairData owner lambda a c
    negativeBasis positiveBasis outputBasis globalBasis
  rw [PositiveTrace.BasisHilbertSchmidtPairData.ordinaryTraceAlong_traceProduct_eq_cyclic
    outputBasis translated]
  rw [PositiveTrace.BasisHilbertSchmidtPairData.ordinaryTraceAlong_traceProduct_eq_cyclic
    outputBasis original]
  apply congrArg (PositiveTrace.ordinaryTraceAlong outputBasis)
  unfold translated original translatedCompactRootPairData
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  apply congrArg
    (pairData owner.sourceTest a c negativeBasis positiveBasis outputBasis
      globalBasis).right
  simpa only using cc20GlobalLogTranslation_neg_apply
    (Real.log lambda)
    ((pairData owner.sourceTest a c negativeBasis positiveBasis outputBasis
      globalBasis).left.adjoint u)

/-- The transported compact pair is exactly the genuine selected-detector
crossing through the actual CCM24 radial support projection. -/
theorem translatedCompactRootPairData_traceProduct_eq_radialOrientedCrossing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).traceProduct =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L detectorOperator owner ∘L
        radialSupportProjection lambda := by
  rw [translatedCompactRootPairData_traceProduct_eq]
  rw [pairData_traceProduct_eq_genuineOrientedBoundaryCrossing
      owner.sourceTest a c hac hsupp negativeBasis positiveBasis outputBasis
        globalBasis]
  exact (detectorRadialOrientedCrossing_eq_translation_conjugation
    owner lambda).symm

/-- The actual radial oriented crossing is trace class along the named global
basis, with the transported compact pair as its witness. -/
theorem detectorRadialOrientedCrossing_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L detectorOperator owner ∘L
        radialSupportProjection lambda) := by
  rw [← translatedCompactRootPairData_traceProduct_eq_radialOrientedCrossing
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis]
  exact translatedCompactRootPairData_isTraceClassAlong
    owner lambda a c negativeBasis positiveBasis outputBasis globalBasis

/-- The ordinary trace of the actual radial crossing is the trace of the
fixed zero-boundary compact pair. -/
theorem ordinaryTraceAlong_detectorRadialOrientedCrossing_eq_pairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
            radialSupportProjection lambda) ∘L detectorOperator owner ∘L
          radialSupportProjection lambda) =
      PositiveTrace.ordinaryTraceAlong globalBasis
        (pairData owner.sourceTest a c negativeBasis positiveBasis
          outputBasis globalBasis).traceProduct := by
  rw [← translatedCompactRootPairData_traceProduct_eq_radialOrientedCrossing
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis]
  exact ordinaryTraceAlong_translatedCompactRootPairData_eq
    owner lambda a c negativeBasis positiveBasis outputBasis globalBasis

/-- The signed transported compact pair keeps the two crossing orientations
coupled as adjoint minus forward. -/
noncomputable def translatedSignedCompactRootPairOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : Op :=
  (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct.adjoint -
    (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct

/-- The signed transported pair is the actual radial support/detector
commutator on the common-log carrier. -/
theorem translatedSignedCompactRootPairOperator_eq_radialCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    translatedSignedCompactRootPairOperator owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis =
      cc20Commutator (radialSupportProjection lambda)
        (detectorOperator owner) := by
  unfold translatedSignedCompactRootPairOperator
  rw [translatedCompactRootPairData_traceProduct_eq_radialOrientedCrossing
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis]
  exact (cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (radialSupportProjection lambda) (detectorOperator owner)
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)).symm

/-- The genuine radial detector commutator is trace class along the named
global basis. -/
theorem radialDetectorCommutator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20Commutator (radialSupportProjection lambda)
        (detectorOperator owner)) := by
  rw [← translatedSignedCompactRootPairOperator_eq_radialCommutator
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis]
  unfold translatedSignedCompactRootPairOperator
  let crossing :=
    (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct
  have hcrossing : PositiveTrace.IsTraceClassAlong globalBasis crossing :=
    translatedCompactRootPairData_isTraceClassAlong owner lambda a c
      negativeBasis positiveBasis outputBasis globalBasis
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_sub globalBasis _ _
    (CC20Concrete.PositiveTrace.isTraceClassAlong_adjoint
      globalBasis crossing hcrossing)
    hcrossing

/-- Any bounded left/right sandwich of the genuine radial detector
commutator remains trace class.  The proof transports the forward compact
pair and its swapped pair separately, then recombines their signed
difference. -/
theorem radialDetectorCommutator_boundedSandwich_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (left right : Op) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (left ∘L cc20Commutator (radialSupportProjection lambda)
        (detectorOperator owner) ∘L right) := by
  let data := translatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis
  have hforward : PositiveTrace.IsTraceClassAlong globalBasis
      (left ∘L data.traceProduct ∘L right) :=
    data.boundedSandwich_isTraceClassAlong outputBasis left right
  have hreverse : PositiveTrace.IsTraceClassAlong globalBasis
      (left ∘L data.traceProduct.adjoint ∘L right) := by
    have h := data.swap.boundedSandwich_isTraceClassAlong
      outputBasis left right
    rw [data.swap_traceProduct_eq_adjoint] at h
    exact h
  have hsigned := CC20Concrete.PositiveTrace.isTraceClassAlong_sub
    globalBasis _ _ hreverse hforward
  rw [← translatedSignedCompactRootPairOperator_eq_radialCommutator
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis]
  unfold translatedSignedCompactRootPairOperator
  let crossing := data.traceProduct
  have heq : left ∘L (crossing.adjoint - crossing) ∘L right =
      (left ∘L crossing.adjoint ∘L right) -
        (left ∘L crossing ∘L right) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, map_sub]
  rw [heq]
  exact hsigned

/-- The outer branch `E Q [E,W]` in the completed source ledger is trace
class from the compact radial commutator owner. -/
theorem sourceOuterCommutatorBranch_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20OuterCommutatorBranch (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda) (detectorOperator owner)) := by
  unfold cc20OuterCommutatorBranch
  exact radialDetectorCommutator_boundedSandwich_isTraceClassAlong
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis
      (radialSupportProjection lambda ∘L
        sourceFourierSupportProjection lambda)
      (ContinuousLinearMap.id ℂ finiteSCarrier)

/-- The reflected outer branch `[E,W] Q E` is trace class from the same
compact radial owner. -/
theorem sourceReflectedOuterCommutatorBranch_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20ReflectedOuterCommutatorBranch
        (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda) (detectorOperator owner)) := by
  have houter := sourceOuterCommutatorBranch_isTraceClassAlong
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis
  have heq : cc20ReflectedOuterCommutatorBranch
        (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda) (detectorOperator owner) =
      -(cc20OuterCommutatorBranch (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (detectorOperator owner)).adjoint := by
    unfold cc20ReflectedOuterCommutatorBranch
      cc20OuterCommutatorBranch cc20Commutator
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp,
      map_sub, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp,
      (radialSupportProjection_isStarProjection lambda)
        |>.isSelfAdjoint.adjoint_eq,
      (sourceFourierSupportProjection_isStarProjection lambda)
        |>.isSelfAdjoint.adjoint_eq,
      (detectorOperator_isSelfAdjoint owner).adjoint_eq]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
    abel
  rw [heq]
  exact CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg
    globalBasis _
    (CC20Concrete.PositiveTrace.isTraceClassAlong_adjoint
      globalBasis _ houter)

/-- The two completed outer branches are trace class as one signed pair. -/
theorem sourceOuterCommutatorPair_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20OuterCommutatorBranch (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda) (detectorOperator owner) +
        cc20ReflectedOuterCommutatorBranch (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (detectorOperator owner)) := by
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_add globalBasis _ _
    (sourceOuterCommutatorBranch_isTraceClassAlong owner lambda a c hac
      hsupp negativeBasis positiveBasis outputBasis globalBasis)
    (sourceReflectedOuterCommutatorBranch_isTraceClassAlong owner lambda a c
      hac hsupp negativeBasis positiveBasis outputBasis globalBasis)

/-- The still-coupled source remainder after the two compactly owned outer
branches are removed.  The second-support and prolate terms are not estimated
separately. -/
noncomputable def sourceSecondSupportProlateRemainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : Op :=
  cc20SecondSupportCommutatorBranch (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda) (detectorOperator owner) -
    cc20ProlateCommutatorBranch (sourceProlateRemainder lambda)
      (detectorOperator owner)

/-- The remaining source owner in explicit scattering form.  The transformed
radial commutator and the prolate commutator stay in one signed difference. -/
theorem sourceSecondSupportProlateRemainder_eq_scatteringDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceSecondSupportProlateRemainder owner lambda =
      radialSupportProjection lambda ∘L
          (archimedeanHardyTitchmarshOperator ∘L
            cc20Commutator (radialSupportProjection lambda)
              (hardyTitchmarshConjugatedDetector owner) ∘L
            archimedeanHardyTitchmarshOperator) ∘L
          radialSupportProjection lambda -
        cc20Commutator (sourceProlateRemainder lambda)
          (detectorOperator owner) := by
  unfold sourceSecondSupportProlateRemainder
    cc20SecondSupportCommutatorBranch cc20ProlateCommutatorBranch
  rw [sourceSecondSupportCommutator_eq_hardyTitchmarsh_conjugation]

/-- The still-coupled second-support/prolate remainder is skew-adjoint. -/
theorem sourceSecondSupportProlateRemainder_adjoint_eq_neg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (sourceSecondSupportProlateRemainder owner lambda).adjoint =
      -sourceSecondSupportProlateRemainder owner lambda := by
  unfold sourceSecondSupportProlateRemainder
    cc20SecondSupportCommutatorBranch cc20ProlateCommutatorBranch
  rw [map_sub, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    (radialSupportProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq]
  rw [cc20Commutator_adjoint_eq_neg
    (sourceFourierSupportProjection lambda) (detectorOperator owner)
    (sourceFourierSupportProjection_isStarProjection lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)]
  rw [cc20Commutator_adjoint_eq_neg
    (sourceProlateRemainder lambda) (detectorOperator owner)
    (sourceProlateRemainder_isPositive lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, map_neg]
  abel

/-- Exact recombination of the completed source ledger into the closed outer
pair and the still-coupled second-support/prolate remainder. -/
theorem sourceThreeBranchCommutator_eq_outerPair_add_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) =
      (cc20OuterCommutatorBranch (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda) (detectorOperator owner) +
        cc20ReflectedOuterCommutatorBranch (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda) (detectorOperator owner)) +
        sourceSecondSupportProlateRemainder owner lambda := by
  unfold cc20ThreeBranchCommutator sourceSecondSupportProlateRemainder
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  abel

/-- Trace legality of the complete source ledger is reduced to the single
coupled second-support/prolate remainder; both outer branches are discharged
by the compact root pair. -/
theorem sourceThreeBranchCommutator_isTraceClassAlong_of_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hremainder : PositiveTrace.IsTraceClassAlong globalBasis
      (sourceSecondSupportProlateRemainder owner lambda)) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner)) := by
  rw [sourceThreeBranchCommutator_eq_outerPair_add_remainder]
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_add globalBasis _ _
    (sourceOuterCommutatorPair_isTraceClassAlong owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis globalBasis)
    hremainder

/-- The radial detector commutator trace keeps the reverse and forward
crossings coupled as conjugate minus original. -/
theorem ordinaryTraceAlong_radialDetectorCommutator_eq_star_sub
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20Commutator (radialSupportProjection lambda)
          (detectorOperator owner)) =
      star (PositiveTrace.ordinaryTraceAlong globalBasis
        (pairData owner.sourceTest a c negativeBasis positiveBasis
          outputBasis globalBasis).traceProduct) -
      PositiveTrace.ordinaryTraceAlong globalBasis
        (pairData owner.sourceTest a c negativeBasis positiveBasis
          outputBasis globalBasis).traceProduct := by
  rw [← translatedSignedCompactRootPairOperator_eq_radialCommutator
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis]
  unfold translatedSignedCompactRootPairOperator
  let crossing :=
    (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct
  have hcrossing : PositiveTrace.IsTraceClassAlong globalBasis crossing :=
    translatedCompactRootPairData_isTraceClassAlong owner lambda a c
      negativeBasis positiveBasis outputBasis globalBasis
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong_sub globalBasis _ _
    (CC20Concrete.PositiveTrace.isTraceClassAlong_adjoint
      globalBasis crossing hcrossing) hcrossing]
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong_adjoint]
  rw [ordinaryTraceAlong_translatedCompactRootPairData_eq
    owner lambda a c negativeBasis positiveBasis outputBasis globalBasis]

end CCM24RadialBoundaryPairTransport
end CCM25Concrete
end Source
end ConnesWeilRH
