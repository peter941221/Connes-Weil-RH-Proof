/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24RadialBoundaryPairTransport

/-!
# Reflected compact root for the CCM24 second support

The Hardy--Titchmarsh conjugate of the selected detector reflects its
Fourier multiplier.  This file realizes that reflected multiplier as the
positive convolution square of the explicit compact root `g(-x)`, then
reuses the compact half-line pair at the actual radial boundary.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24ReflectedCompactRoot

open MeasureTheory
open scoped ENNReal FourierTransform InnerProduct
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.CompactConvolutionSupport
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24RadialBoundaryPairTransport
open SelectedCrossingOperatorBridge

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- Fourier transform of the reflected convolution square is the reflected
Fourier multiplier of the original square. -/
theorem fourier_reflection_convolutionSquare_apply
    (g : CompactLogConvolution.CompactLogTest) (xi : ℝ) :
    (𝓕 g.reflection.convolutionSquare.test) xi =
      (𝓕 g.convolutionSquare.test) (-xi) := by
  calc
    (𝓕 g.reflection.convolutionSquare.test) xi =
        𝓕 (fun x : ℝ => g.convolutionSquare.test (-x)) xi := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact g.reflection_convolutionSquare_apply x
    _ = (𝓕 g.convolutionSquare.test) (-xi) := by
      change 𝓕 ((g.convolutionSquare.test : ℝ → ℂ) ∘
        LinearIsometryEquiv.neg ℝ) xi = _
      exact Real.fourier_comp_linearIsometry
        (LinearIsometryEquiv.neg ℝ)
        (g.convolutionSquare.test : ℝ → ℂ) xi

/-- Conjugating the original Fourier multiplier by spectral reflection is
the multiplier of the explicit reflected compact root. -/
theorem reflectedFourierMultiplier_eq_reflection_conjugation
    (g : CompactLogConvolution.CompactLogTest) :
    cc20FourierMultiplier g.reflection.convolutionSquare.test =
      logSpectralReflectionOperator ∘L
        cc20FourierMultiplier g.convolutionSquare.test ∘L
          logSpectralReflectionOperator := by
  apply ContinuousLinearMap.ext
  intro u
  unfold logSpectralReflectionOperator
  simp only [ContinuousLinearMap.comp_apply, cc20FourierMultiplier_apply]
  change ((𝓕 g.reflection.convolutionSquare.test).toLp ⊤ • u :
      finiteSCarrier) =
    ccm24LogSpectralReflection
      (((𝓕 g.convolutionSquare.test).toLp ⊤) •
        ccm24LogSpectralReflection u)
  rw [Lp.ext_iff]
  have hleft := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
    ((𝓕 g.reflection.convolutionSquare.test).toLp ⊤) u
  have hleftMultiplier :=
    SchwartzMap.coeFn_toLp (𝓕 g.reflection.convolutionSquare.test) ⊤
  have houter := ccm24LogSpectralReflectionEquiv_coeFn
    (((𝓕 g.convolutionSquare.test).toLp ⊤) •
      ccm24LogSpectralReflection u)
  have hinner := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
    ((𝓕 g.convolutionSquare.test).toLp ⊤)
      (ccm24LogSpectralReflection u)
  have hinnerNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq hinner
  have horiginalMultiplier :=
    SchwartzMap.coeFn_toLp (𝓕 g.convolutionSquare.test) ⊤
  have horiginalMultiplierNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      horiginalMultiplier
  have hreflection := ccm24LogSpectralReflectionEquiv_coeFn u
  have hreflectionNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      hreflection
  filter_upwards [hleft, hleftMultiplier, houter, hinnerNeg,
      horiginalMultiplierNeg, hreflectionNeg] with xi hleftAt
      hleftMultiplierAt houterAt hinnerAt horiginalMultiplierAt
      hreflectionAt
  simp only [Function.comp_apply, Pi.smul_apply'] at hinnerAt horiginalMultiplierAt hreflectionAt
  rw [hleftAt, houterAt, hinnerAt]
  simp only [Pi.smul_apply']
  rw [hleftMultiplierAt, horiginalMultiplierAt, hreflectionAt]
  simp only [smul_eq_mul, neg_neg]
  rw [fourier_reflection_convolutionSquare_apply]

/-- The spectral detector produced by Hardy--Titchmarsh conjugation is
ordinary whole-line convolution by the reflected compact square. -/
theorem reflectedSpectralDetector_eq_reflectedConvolutionSquare
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    reflectedSpectralDetector owner =
      cc20GlobalLogConvolution
        owner.sourceTest.reflection.convolutionSquare.test := by
  apply ContinuousLinearMap.ext
  intro u
  unfold reflectedSpectralDetector cc20GlobalLogConvolution
    globalLogFourierOperator globalLogFourierInverseOperator
    logSpectralReflectionOperator
  simp only [ContinuousLinearMap.comp_apply]
  have hmultiplier := congrArg
    (fun T : Op => T ((Lp.fourierTransformₗᵢ ℝ ℂ) u))
    (reflectedFourierMultiplier_eq_reflection_conjugation owner.sourceTest)
  simp only [ContinuousLinearMap.comp_apply,
    logSpectralReflectionOperator] at hmultiplier
  exact congrArg (Lp.fourierTransformₗᵢ ℝ ℂ).symm hmultiplier.symm

/-- The reflected spectral detector is the positive square of an explicit
compact root, rather than an abstract reflected multiplier. -/
theorem reflectedSpectralDetector_eq_reflectedPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    reflectedSpectralDetector owner =
      cc20GlobalConvolutionPositive
        owner.sourceTest.reflection.involution.test := by
  rw [reflectedSpectralDetector_eq_reflectedConvolutionSquare]
  exact (globalConvolutionPositive_eq_convolutionSquare
    owner.sourceTest.reflection).symm

theorem hardyTitchmarshConjugatedDetector_eq_reflectedPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    hardyTitchmarshConjugatedDetector owner =
      cc20GlobalConvolutionPositive
        owner.sourceTest.reflection.involution.test := by
  rw [hardyTitchmarshConjugatedDetector_eq_reflectedSpectralDetector]
  exact reflectedSpectralDetector_eq_reflectedPositive owner

/-- Every positive compact-root convolution square commutes with logarithmic
translation. -/
theorem reflectedPositive_comp_translation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (b : ℝ) :
    cc20GlobalConvolutionPositive
        owner.sourceTest.reflection.involution.test ∘L
          (cc20GlobalLogTranslation b).toContinuousLinearMap =
      (cc20GlobalLogTranslation b).toContinuousLinearMap ∘L
        cc20GlobalConvolutionPositive
          owner.sourceTest.reflection.involution.test := by
  let g := owner.sourceTest.reflection
  let C := cc20GlobalLogConvolution g.involution.test
  let U := (cc20GlobalLogTranslation b).toContinuousLinearMap
  let Uinv := (cc20GlobalLogTranslation (-b)).toContinuousLinearMap
  have hC : C ∘L U = U ∘L C := by
    simpa only [neg_neg] using
      (cc20GlobalLogConvolution_comp_translation_neg_eq g (-b))
  have hCinv : C ∘L Uinv = Uinv ∘L C := by
    exact cc20GlobalLogConvolution_comp_translation_neg_eq g b
  have hCadj : C† ∘L U = U ∘L C† := by
    have h := congrArg (fun operator => ContinuousLinearMap.adjoint operator)
      hCinv
    simpa [U, Uinv, ContinuousLinearMap.adjoint_comp,
      cc20GlobalLogTranslation_neg_adjoint] using h.symm
  change C† ∘L C ∘L U = U ∘L (C† ∘L C)
  calc
    C† ∘L C ∘L U = C† ∘L (C ∘L U) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = C† ∘L (U ∘L C) := by rw [hC]
    _ = (C† ∘L U) ∘L C := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = (U ∘L C†) ∘L C := by rw [hCadj]
    _ = U ∘L (C† ∘L C) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl

/-- The reflected detector crossing at the radial cutoff is the translated
zero-boundary crossing of the explicit reflected positive root. -/
theorem reflectedDetectorRadialOrientedCrossing_eq_translation_conjugation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (ContinuousLinearMap.id ℂ finiteSCarrier -
        radialSupportProjection lambda) ∘L
          hardyTitchmarshConjugatedDetector owner ∘L
        radialSupportProjection lambda =
      (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap ∘L
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
            cc20PositiveHalfLineProjection) ∘L
          cc20GlobalConvolutionPositive
            owner.sourceTest.reflection.involution.test ∘L
          cc20PositiveHalfLineProjection) ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
  rw [hardyTitchmarshConjugatedDetector_eq_reflectedPositive]
  exact ccm24RadialOrientedCrossing_eq_translation_conjugation lambda _
    (reflectedPositive_comp_translation owner (-Real.log lambda))

/-- Transport the compact pair of the reflected root to the CCM24 radial
cutoff. -/
noncomputable def reflectedTranslatedCompactRootPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))))
      globalBasis :=
  (pairData owner.sourceTest.reflection (-c) (-a) negativeBasis positiveBasis
    outputBasis globalBasis).boundedSandwich outputBasis
      (cc20GlobalLogTranslation
        (-Real.log lambda)).toContinuousLinearMap
      (cc20GlobalLogTranslation
        (Real.log lambda)).toContinuousLinearMap

theorem reflectedTranslatedCompactRootPairData_traceProduct_eq_radialCrossing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).traceProduct =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        radialSupportProjection lambda) ∘L
          hardyTitchmarshConjugatedDetector owner ∘L
        radialSupportProjection lambda := by
  unfold reflectedTranslatedCompactRootPairData
  rw [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
  rw [pairData_traceProduct_eq_genuineOrientedBoundaryCrossing
    owner.sourceTest.reflection (-c) (-a) (by linarith)
    (owner.sourceTest.reflection_support_subset_Icc a c hsupp)
    negativeBasis positiveBasis outputBasis globalBasis]
  exact (reflectedDetectorRadialOrientedCrossing_eq_translation_conjugation
    owner lambda).symm

/-- The actual radial crossing of the Hardy--Titchmarsh-conjugated detector
has a compact Hilbert--Schmidt pair witness. -/
theorem reflectedDetectorRadialOrientedCrossing_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
        radialSupportProjection lambda) ∘L
          hardyTitchmarshConjugatedDetector owner ∘L
        radialSupportProjection lambda) := by
  rw [← reflectedTranslatedCompactRootPairData_traceProduct_eq_radialCrossing
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis]
  exact (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis).traceProduct_isTraceClassAlong

/-- Sandwich the reflected radial pair by the actual Hardy--Titchmarsh
unitary.  Its trace product lives on the genuine source second support. -/
noncomputable def sourceSecondSupportCompactRootPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))))
      globalBasis :=
  (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis).boundedSandwich outputBasis
      archimedeanHardyTitchmarshOperator
      archimedeanHardyTitchmarshOperator

theorem sourceSecondSupportCompactRootPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (sourceSecondSupportCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct =
      cc20OrientedBoundaryCrossing (sourceFourierSupportProjection lambda)
        (detectorOperator owner) := by
  unfold sourceSecondSupportCompactRootPairData
  rw [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
  rw [reflectedTranslatedCompactRootPairData_traceProduct_eq_radialCrossing
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis]
  exact (sourceSecondSupportOrientedCrossing_eq_hardyTitchmarsh_conjugation
    owner lambda).symm

/-- The genuine source second-support crossing is trace class with no stored
analytic premise. -/
theorem sourceSecondSupportOrientedCrossing_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (cc20OrientedBoundaryCrossing (sourceFourierSupportProjection lambda)
        (detectorOperator owner)) := by
  rw [← sourceSecondSupportCompactRootPairData_traceProduct_eq owner lambda
    a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis]
  exact (sourceSecondSupportCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis).traceProduct_isTraceClassAlong

/-- Both orientations of the genuine source second-support boundary are
trace class.  This is a legality theorem; later estimates still retain the
prolate commutator in the same signed owner. -/
theorem sourceSecondSupportCommutator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (cc20Commutator (sourceFourierSupportProjection lambda)
        (detectorOperator owner)) := by
  let crossing := cc20OrientedBoundaryCrossing
    (sourceFourierSupportProjection lambda) (detectorOperator owner)
  have hcrossing : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      crossing :=
    sourceSecondSupportOrientedCrossing_isTraceClassAlong owner lambda a c
      hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  rw [cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (sourceFourierSupportProjection lambda) (detectorOperator owner)
    (sourceFourierSupportProjection_isStarProjection lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)]
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_sub globalBasis _ _
    (CC20Concrete.PositiveTrace.isTraceClassAlong_adjoint globalBasis _
      hcrossing)
    hcrossing

/-- After the reflected root is made explicit, the coupled
second-support/prolate remainder is exactly the genuine Sonin commutator
minus the two already-owned outer branches.  This identity keeps the prolate
cancellation intact and exposes the only remaining legality owner. -/
theorem sourceSecondSupportProlateRemainder_eq_sonin_sub_outerPair
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceSecondSupportProlateRemainder owner lambda =
      cc20Commutator (sourceSoninProjection lambda) (detectorOperator owner) -
        (cc20OuterCommutatorBranch (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda) (detectorOperator owner) +
          cc20ReflectedOuterCommutatorBranch (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (detectorOperator owner)) := by
  rw [sourceSoninCommutator_eq_threeBranch]
  rw [sourceThreeBranchCommutator_eq_outerPair_add_remainder]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  abel

end CCM24ReflectedCompactRoot
end CCM25Concrete
end Source
end ConnesWeilRH
