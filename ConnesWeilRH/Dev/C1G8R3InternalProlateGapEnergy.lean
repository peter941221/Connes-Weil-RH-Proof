/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3RadialBoundaryEnergy
import ConnesWeilRH.Dev.C1G8R3RadialBoundaryGapSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
import ConnesWeilRH.Source.CCM25Concrete.CCM24ReflectedCompactRoot
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle
import ConnesWeilRH.Dev.C1G8R3ScaleDetectorRootSquareSum

/-!
# Source-basis energy of the internal prolate gap

The internal radial-but-non-Sonin gap is reduced to the sum of the source
prolate Hilbert--Schmidt leg and a compact-root crossing of the second support.
This is the same healthy-`CompactLog` B5 consumer as the preceding G8 R3
energy leaves.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.CompactConvolutionSupport
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24ReflectedCompactRoot
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare
open scoped ENNReal FourierTransform InnerProduct InnerProductSpace

local notation "Carrier" => finiteSCarrier

noncomputable local instance internalGapSourceCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Hardy--Titchmarsh transport of the root -/

theorem rootTest_reflection_involution_eq
    (g : CompactLogConvolution.CompactLogTest) :
    g.reflection.involution.test = g.involution.reflection.test := by
  apply SchwartzMap.ext
  simp [CompactLogConvolution.CompactLogTest.reflection_apply,
    CompactLogConvolution.CompactLogTest.involution_apply]

theorem rootTest_reflection_fourier_apply
    (g : CompactLogConvolution.CompactLogTest) (xi : ℝ) :
    (𝓕 g.reflection.test) xi = (𝓕 g.test) (-xi) := by
  calc
    (𝓕 g.reflection.test) xi =
        𝓕 (fun x : ℝ => g.test (-x)) xi := by
          apply Real.fourier_congr_ae
          filter_upwards with x
          exact g.reflection_apply x
    _ = (𝓕 g.test) (-xi) := by
      change 𝓕 ((g.test : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ) xi = _
      exact Real.fourier_comp_linearIsometry
        (LinearIsometryEquiv.neg ℝ) g.test xi

theorem reflectedRootFourierMultiplier_eq_reflection_conjugation
    (g : CompactLogConvolution.CompactLogTest) :
    cc20FourierMultiplier g.reflection.involution.test =
      logSpectralReflectionOperator ∘L
        cc20FourierMultiplier g.involution.test ∘L
          logSpectralReflectionOperator := by
  rw [rootTest_reflection_involution_eq]
  apply ContinuousLinearMap.ext
  intro u
  unfold logSpectralReflectionOperator
  simp only [ContinuousLinearMap.comp_apply, cc20FourierMultiplier_apply]
  change ((𝓕 g.involution.reflection.test).toLp ⊤ • u : Carrier) =
    ccm24LogSpectralReflection
      (((𝓕 g.involution.test).toLp ⊤) •
        ccm24LogSpectralReflection u)
  rw [Lp.ext_iff]
  have hleft := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
    ((𝓕 g.involution.reflection.test).toLp ⊤) u
  have hleftMultiplier :=
    SchwartzMap.coeFn_toLp (𝓕 g.involution.reflection.test) ⊤
  have houter := ccm24LogSpectralReflectionEquiv_coeFn
    (((𝓕 g.involution.test).toLp ⊤) •
      ccm24LogSpectralReflection u)
  have hinner := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
    ((𝓕 g.involution.test).toLp ⊤)
      (ccm24LogSpectralReflection u)
  have hinnerNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq hinner
  have horiginalMultiplier :=
    SchwartzMap.coeFn_toLp (𝓕 g.involution.test) ⊤
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
  simp only [Function.comp_apply, Pi.smul_apply'] at hinnerAt
  simp only [Function.comp_apply] at horiginalMultiplierAt
  simp only [Function.comp_apply] at hreflectionAt
  rw [hleftAt, houterAt, hinnerAt]
  simp only [Pi.smul_apply']
  rw [hleftMultiplierAt, horiginalMultiplierAt, hreflectionAt]
  simp only [smul_eq_mul, neg_neg]
  rw [rootTest_reflection_fourier_apply]

theorem hardyTitchmarsh_conjugate_root_eq_reflected_root
    (g : CompactLogConvolution.CompactLogTest) :
    archimedeanHardyTitchmarshOperator ∘L
        cc20GlobalLogConvolution g.involution.test ∘L
          archimedeanHardyTitchmarshOperator =
      cc20GlobalLogConvolution g.reflection.involution.test := by
  apply ContinuousLinearMap.ext
  intro u
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  simp only [ContinuousLinearMap.comp_apply]
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
      (ccm24ArchimedeanHardyTitchmarsh
        (cc20GlobalLogConvolution g.involution.test
          (ccm24ArchimedeanHardyTitchmarsh u))) =
    (Lp.fourierTransformₗᵢ ℝ ℂ)
      (cc20GlobalLogConvolution g.reflection.involution.test u)
  rw [ccm24ArchimedeanHardyTitchmarsh_fourier_readback,
    fourier_globalLogConvolution,
    ccm24ArchimedeanHardyTitchmarsh_fourier_readback,
    fourier_globalLogConvolution]
  let z := (Lp.fourierTransformₗᵢ ℝ ℂ) u
  let A := cc20FourierMultiplier g.involution.test
  have hcommAt := congrArg
    (fun T : Carrier →L[ℂ] Carrier => T (ccm24LogSpectralReflection z))
    (archimedeanScatteringMultiplier_comp_fourierMultiplier
      g.involution.test)
  simp only [ContinuousLinearMap.comp_apply] at hcommAt
  have hcomm : A (ccm24ArchimedeanScatteringMultiplier
      (ccm24LogSpectralReflection z)) =
      ccm24ArchimedeanScatteringMultiplier (A (ccm24LogSpectralReflection z)) := by
    simpa only [A] using hcommAt.symm
  have hcancel := ccm24ArchimedeanSpectralScattering_involutive
    (ccm24LogSpectralReflection (A (ccm24LogSpectralReflection z)))
  have hreflect : ccm24LogSpectralReflection
        (ccm24LogSpectralReflection (A (ccm24LogSpectralReflection z))) =
      A (ccm24LogSpectralReflection z) := by
    exact ccm24LogSpectralReflection_involutive _
  rw [hreflect] at hcancel
  have hleft :
      ccm24ArchimedeanScatteringMultiplier
        (ccm24LogSpectralReflection
          (A (ccm24ArchimedeanScatteringMultiplier
            (ccm24LogSpectralReflection z)))) =
        ccm24LogSpectralReflection (A (ccm24LogSpectralReflection z)) := by
    rw [hcomm]
    exact hcancel
  have hmultiplier := congrArg
    (fun T : Carrier →L[ℂ] Carrier => T z)
    (reflectedRootFourierMultiplier_eq_reflection_conjugation g)
  simp only [ContinuousLinearMap.comp_apply] at hmultiplier
  change ccm24ArchimedeanScatteringMultiplier
      (ccm24LogSpectralReflection
        (A (ccm24ArchimedeanScatteringMultiplier
          (ccm24LogSpectralReflection z)))) =
    cc20FourierMultiplier g.reflection.involution.test z
  rw [hleft]
  exact hmultiplier.symm

noncomputable def reflectedSelectedRootOwner
    (owner : SelectedWeilSquareOwner) : SelectedWeilSquareOwner :=
  SelectedWeilSquareOwner.ofCompactLogTest owner.sourceTest.reflection

private noncomputable def internalGapBasisIndex
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : Set G :=
  Classical.choose (exists_hilbertBasis ℂ G)

private noncomputable def internalGapBasis
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : HilbertBasis (internalGapBasisIndex G) ℂ G :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ G))

theorem reflectedRoot_radialCrossing_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Summable fun i : ρ =>
      ‖(((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
          rootConvolution (reflectedSelectedRootOwner owner) ∘L
          radialSupportProjection lambda ∘L
          (archimedeanHardyTitchmarshOperator ∘L sourceInclusion lambda))
        (sourceBasis i))‖ ^ 2 := by
  let rootOwner := reflectedSelectedRootOwner owner
  let globalBasis := internalGapBasis Carrier
  let inputBasis := internalGapBasis
    (Lp ℂ 2 (volume : Measure
      (CompactInputInterval
        (-selectedRootSupportRadius rootOwner)
        (selectedRootSupportRadius rootOwner)
        (-selectedRootSupportRadius rootOwner) 0)))
  let outputBasis := internalGapBasis
    (Lp ℂ 2 (volume : Measure
      (CompactOutputInterval (-selectedRootSupportRadius rootOwner) 0)))
  let window := selectedRootBoundaryWindowOperator rootOwner
  let toBoundary := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  let fromBoundary := (cc20GlobalLogTranslation
    (-Real.log lambda)).toContinuousLinearMap
  have hwindow : Summable fun i => ‖window (globalBasis i)‖ ^ 2 := by
    exact selectedRootBoundaryWindowOperator_basis_normSq_summable
      rootOwner inputBasis outputBasis globalBasis
  have hcommute : rootConvolution rootOwner ∘L fromBoundary =
      fromBoundary ∘L rootConvolution rootOwner := by
    exact cc20GlobalLogConvolution_comp_translation_neg_eq rootOwner.sourceTest
      (Real.log lambda)
  have hcross :
      (ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
          rootConvolution rootOwner ∘L radialSupportProjection lambda =
        fromBoundary ∘L window ∘L toBoundary := by
    change (ContinuousLinearMap.id ℂ Carrier -
        ccm24LogRadialSupportProjection lambda) ∘L
          rootConvolution rootOwner ∘L
          ccm24LogRadialSupportProjection lambda = _
    rw [ccm24RadialOrientedCrossing_eq_translation_conjugation
      lambda (rootConvolution rootOwner) hcommute]
    rw [← selectedRoot_zeroBoundaryCrossing_eq_finiteWindow rootOwner]
  have hpre : Summable fun i : ρ =>
      ‖(window ∘L toBoundary ∘L archimedeanHardyTitchmarshOperator ∘L
          sourceInclusion lambda) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp globalBasis globalBasis
      sourceBasis window
      (toBoundary ∘L archimedeanHardyTitchmarshOperator ∘L
        sourceInclusion lambda) hwindow
  have hpost : Summable fun i : ρ =>
      ‖(fromBoundary ∘L window ∘L toBoundary ∘L
          archimedeanHardyTitchmarshOperator ∘L sourceInclusion lambda)
        (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_postcomp sourceBasis
      (window ∘L toBoundary ∘L archimedeanHardyTitchmarshOperator ∘L
        sourceInclusion lambda) fromBoundary hpre
  refine Summable.congr hpost ?_
  intro i
  congr 2
  have hvector := congrArg
    (fun T : Carrier →L[ℂ] Carrier =>
      T ((archimedeanHardyTitchmarshOperator ∘L sourceInclusion lambda)
        (sourceBasis i))) hcross
  simpa only [rootOwner, window, toBoundary, fromBoundary,
    ContinuousLinearMap.comp_apply] using hvector.symm

/-- Hardy--Titchmarsh carries the reflected root's radial crossing back to
the original root's second-support leakage.  The source inclusion is fixed
by the second-support projection because the Sonin subspace lies in their
intersection. -/
theorem reflectedRoot_radialCrossing_conjugates_to_fourierLeakage
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    archimedeanHardyTitchmarshOperator ∘L
        ((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
          rootConvolution (reflectedSelectedRootOwner owner) ∘L
          radialSupportProjection lambda ∘L
          archimedeanHardyTitchmarshOperator ∘L sourceInclusion lambda) =
      (ContinuousLinearMap.id ℂ Carrier -
        sourceFourierSupportProjection lambda) ∘L
        rootConvolution owner ∘L sourceInclusion lambda := by
  let H := archimedeanHardyTitchmarshOperator
  let E := radialSupportProjection lambda
  let Q := sourceFourierSupportProjection lambda
  let P := sourceSoninProjection lambda
  let J := sourceInclusion lambda
  have hHH : H ∘L H = ContinuousLinearMap.id ℂ Carrier := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, H]
    exact archimedeanHardyTitchmarshOperator_involutive u
  have hbase := hardyTitchmarsh_conjugate_root_eq_reflected_root
    owner.sourceTest
  have hbaseRoot : H ∘L rootConvolution owner ∘L H =
      rootConvolution (reflectedSelectedRootOwner owner) := by
    change H ∘L cc20GlobalLogConvolution
        owner.sourceTest.involution.test ∘L H =
      cc20GlobalLogConvolution owner.sourceTest.reflection.involution.test
    exact hbase
  have hHCref : H ∘L rootConvolution (reflectedSelectedRootOwner owner) =
      rootConvolution owner ∘L H := by
    apply ContinuousLinearMap.ext
    intro u
    have hAt := congrArg (fun T : Carrier →L[ℂ] Carrier => T u) hbaseRoot
    simp only [ContinuousLinearMap.comp_apply] at hAt
    have hApply := congrArg H hAt
    simpa only [ContinuousLinearMap.comp_apply, H,
      archimedeanHardyTitchmarshOperator_involutive] using hApply.symm
  have hleftProjection : H ∘L
      (ContinuousLinearMap.id ℂ Carrier - E) =
      (ContinuousLinearMap.id ℂ Carrier - Q) ∘L H := by
    change H ∘L (ContinuousLinearMap.id ℂ Carrier -
        radialSupportProjection lambda) =
      (ContinuousLinearMap.id ℂ Carrier -
        sourceFourierSupportProjection lambda) ∘L H
    rw [sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, H]
    rw [map_sub]
    congr 1
    exact congrArg (fun v : Carrier => H (E v))
      (archimedeanHardyTitchmarshOperator_involutive u).symm
  have hQPmul : sourceFourierSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    letI : CompleteSpace
        ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule ⊓
          (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule :
          Submodule ℂ Carrier) :=
      (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.right_starProjection_absorbs_intersection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  have hQP : Q ∘L P = P := by
    simpa only [ContinuousLinearMap.mul_def, Q, P] using hQPmul
  have hQJ : Q ∘L J = J := by
    apply ContinuousLinearMap.ext
    intro u
    have hPJ := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
      T u) (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
    simp only [ContinuousLinearMap.comp_apply] at hPJ
    have hQPJ := congrArg (fun T : Carrier →L[ℂ] Carrier => T (J u)) hQP
    simp only [ContinuousLinearMap.comp_apply] at hQPJ
    change Q (J u) = J u
    calc
      Q (J u) = Q (P (J u)) :=
        congrArg (fun v : Carrier => Q v) hPJ.symm
      _ = P (J u) := hQPJ
      _ = J u := hPJ
  apply ContinuousLinearMap.ext
  intro u
  change H ((ContinuousLinearMap.id ℂ Carrier - E)
      (rootConvolution (reflectedSelectedRootOwner owner)
        (E (H (J u))))) =
    (ContinuousLinearMap.id ℂ Carrier - Q)
      (rootConvolution owner (J u))
  have hleftAt := congrArg
    (fun T : Carrier →L[ℂ] Carrier =>
      T (rootConvolution (reflectedSelectedRootOwner owner)
        (E (H (J u))))) hleftProjection
  have hrootAt := congrArg
    (fun T : Carrier →L[ℂ] Carrier => T (E (H (J u)))) hHCref
  have hQJAt := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
    T u) hQJ
  have hQAt : H (E (H (J u))) = J u := by
    simpa only [sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation,
      ContinuousLinearMap.comp_apply, H, E, Q, J] using hQJAt
  simp only [ContinuousLinearMap.comp_apply] at hleftAt hrootAt
  calc
    H ((ContinuousLinearMap.id ℂ Carrier - E)
        (rootConvolution (reflectedSelectedRootOwner owner)
          (E (H (J u))))) =
        (ContinuousLinearMap.id ℂ Carrier - Q)
          (H (rootConvolution (reflectedSelectedRootOwner owner)
            (E (H (J u))))) := hleftAt
    _ = (ContinuousLinearMap.id ℂ Carrier - Q)
          (rootConvolution owner (H (E (H (J u))))) := by rw [hrootAt]
    _ = (ContinuousLinearMap.id ℂ Carrier - Q)
          (rootConvolution owner (J u)) := by rw [hQAt]

/-- The full selected-root image of the source quotient band is
Hilbert--Schmidt on every source basis.  Its two summands are the adjoint of
the prolate factor and the reflected compact-root crossing. -/
theorem sourceBand_rootSourceLeg_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Summable fun i : ρ =>
      ‖(sourceBandProjection lambda ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2 := by
  let globalBasis := internalGapBasis Carrier
  let E := radialSupportProjection lambda
  let Q := sourceFourierSupportProjection lambda
  let B := sourceBandProjection lambda
  let C := rootConvolution owner
  let J := sourceInclusion lambda
  let K := sourceProlateHilbertSchmidtFactor lambda
  have hK : Summable fun i => ‖K (globalBasis i)‖ ^ 2 := by
    exact sourceProlateHilbertSchmidtFactor_summable_all_scales
      globalBasis lambda
  have hKadj : Summable fun i => ‖K.adjoint (globalBasis i)‖ ^ 2 := by
    exact BasisHilbertSchmidtPairData.summable_adjoint_normSq
      globalBasis globalBasis K hK
  have hfirst : Summable fun i : ρ =>
      ‖(K.adjoint ∘L C ∘L J) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp globalBasis globalBasis
      sourceBasis K.adjoint (C ∘L J) hKadj
  have hcross : Summable fun i : ρ =>
      ‖(((ContinuousLinearMap.id ℂ Carrier - E) ∘L
          rootConvolution (reflectedSelectedRootOwner owner) ∘L E ∘L
          archimedeanHardyTitchmarshOperator ∘L J)
        (sourceBasis i))‖ ^ 2 := by
    exact reflectedRoot_radialCrossing_summable owner lambda sourceBasis
  have hfourierConjugate : Summable fun i : ρ =>
      ‖(archimedeanHardyTitchmarshOperator ∘L
        ((ContinuousLinearMap.id ℂ Carrier - E) ∘L
          rootConvolution (reflectedSelectedRootOwner owner) ∘L E ∘L
          archimedeanHardyTitchmarshOperator ∘L J))
          (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_postcomp sourceBasis
      ((ContinuousLinearMap.id ℂ Carrier - E) ∘L
        rootConvolution (reflectedSelectedRootOwner owner) ∘L E ∘L
        archimedeanHardyTitchmarshOperator ∘L J)
      archimedeanHardyTitchmarshOperator hcross
  have hfourierLeak : Summable fun i : ρ =>
      ‖((ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L J)
        (sourceBasis i)‖ ^ 2 := by
    refine hfourierConjugate.congr ?_
    intro i
    congr 2
    exact congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
      T (sourceBasis i))
      (reflectedRoot_radialCrossing_conjugates_to_fourierLeakage
        owner lambda)
  have hsecond : Summable fun i : ρ =>
      ‖(E ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L J)
        (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_postcomp sourceBasis
      ((ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L J) E hfourierLeak
  have hPQmul : sourceSoninProjection lambda *
      sourceFourierSupportProjection lambda = sourceSoninProjection lambda := by
    letI : CompleteSpace
        ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule ⊓
          (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule :
          Submodule ℂ Carrier) :=
      (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.intersection_absorbs_right_starProjection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  have hPComplement : sourceSoninProjection lambda *
      (1 - sourceFourierSupportProjection lambda) = 0 := by
    rw [mul_sub, mul_one, hPQmul, sub_self]
  have hBq : B ∘L Q = K.adjoint := by
    change sourceBandProjection lambda ∘L
        sourceFourierSupportProjection lambda =
      (sourceFourierSupportProjection lambda ∘L
        sourceBandProjection lambda).adjoint
    rw [ContinuousLinearMap.adjoint_comp,
      (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
      (sourceFourierSupportProjection_isStarProjection lambda)
        |>.isSelfAdjoint.adjoint_eq]
  have hBComplement : B ∘L
      (ContinuousLinearMap.id ℂ Carrier - Q) =
      E ∘L (ContinuousLinearMap.id ℂ Carrier - Q) := by
    change (E - sourceSoninProjection lambda) ∘L
        (ContinuousLinearMap.id ℂ Carrier - Q) =
      E ∘L (ContinuousLinearMap.id ℂ Carrier - Q)
    simpa only [ContinuousLinearMap.mul_def, E, Q] using
      (show (radialSupportProjection lambda - sourceSoninProjection lambda) *
          (1 - sourceFourierSupportProjection lambda) =
        radialSupportProjection lambda *
          (1 - sourceFourierSupportProjection lambda) by
        rw [sub_mul]
        have hzero : sourceSoninProjection lambda *
            (1 - sourceFourierSupportProjection lambda) = 0 :=
          hPComplement
        rw [hzero, sub_zero])
  have hsplit : B ∘L C =
      B ∘L Q ∘L C + B ∘L
        (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C := by
    simpa only [ContinuousLinearMap.mul_def, B, Q, C] using
      (show sourceBandProjection lambda * rootConvolution owner =
          sourceBandProjection lambda * sourceFourierSupportProjection lambda *
            rootConvolution owner +
          sourceBandProjection lambda *
            (1 - sourceFourierSupportProjection lambda) *
              rootConvolution owner by noncomm_ring)
  have hsplitSource : B ∘L C ∘L J =
      B ∘L Q ∘L C ∘L J + B ∘L
        (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L J := by
    apply ContinuousLinearMap.ext
    intro u
    have hu := congrArg
      (fun T : Carrier →L[ℂ] Carrier => T (J u)) hsplit
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply] using hu
  have hsplitFactors : B ∘L C ∘L J =
      K.adjoint ∘L C ∘L J + E ∘L
        (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L J := by
    apply ContinuousLinearMap.ext
    intro u
    have hu := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
      T u) hsplitSource
    have hBqAt := congrArg
      (fun T : Carrier →L[ℂ] Carrier => T (C (J u))) hBq
    have hBcompAt := congrArg
      (fun T : Carrier →L[ℂ] Carrier =>
        T (C (J u)))
      hBComplement
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply] at hu hBqAt hBcompAt ⊢
    rw [hBqAt, hBcompAt] at hu
    exact hu
  rw [hsplitFactors]
  exact PositiveTrace.summable_normSq_add sourceBasis
    (K.adjoint ∘L C ∘L J)
    (E ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L J)
    hfirst hsecond

/-- The full selected-root source-Sonin leakage is Hilbert--Schmidt on every
named source basis, by adding the radial-boundary and internal-gap channels
from the exact split. -/
theorem selectedRoot_sourceSoninLeakage_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Summable fun i : ρ =>
      ‖(((ContinuousLinearMap.id ℂ Carrier - sourceSoninProjection lambda) ∘L
        rootConvolution owner ∘L sourceInclusion lambda) (sourceBasis i))‖ ^ 2 := by
  let radius := selectedRootSupportRadius owner
  let inputBasis := internalGapBasis
    (Lp ℂ 2 (volume : Measure
      (CompactInputInterval (-radius) radius (-radius) 0)))
  let outputBasis := internalGapBasis
    (Lp ℂ 2 (volume : Measure (CompactOutputInterval (-radius) 0)))
  let globalBasis := internalGapBasis Carrier
  have hboundary : Summable fun i : ρ =>
      ‖(((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
        rootConvolution owner ∘L sourceInclusion lambda) (sourceBasis i))‖ ^ 2 := by
    exact selectedRoot_radialBoundary_sourceBasis_normSq_summable
      owner lambda sourceBasis inputBasis outputBasis globalBasis
  have hgap : Summable fun i : ρ =>
      ‖((sourceBandProjection lambda ∘L radialSupportProjection lambda ∘L
        rootConvolution owner ∘L sourceInclusion lambda) (sourceBasis i))‖ ^ 2 := by
    have hbandRadial : sourceBandProjection lambda ∘L
        radialSupportProjection lambda ∘L rootConvolution owner ∘L
          sourceInclusion lambda =
        sourceBandProjection lambda ∘L rootConvolution owner ∘L
          sourceInclusion lambda := by
      apply ContinuousLinearMap.ext
      intro u
      have hpoint := congrArg
        (fun T : Carrier →L[ℂ] Carrier =>
          T (rootConvolution owner (sourceInclusion lambda u)))
        (sourceBandProjection_comp_radialSupportProjection_eq_self lambda)
      simpa only [ContinuousLinearMap.comp_apply] using hpoint
    rw [hbandRadial]
    exact sourceBand_rootSourceLeg_summable owner lambda sourceBasis
  rw [selectedRoot_sourceSoninLeakage_eq_radialBoundary_add_internalGap]
  exact PositiveTrace.summable_normSq_add sourceBasis
    ((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
      rootConvolution owner ∘L sourceInclusion lambda)
    ((sourceBandProjection lambda ∘L radialSupportProjection lambda) ∘L
      rootConvolution owner ∘L sourceInclusion lambda)
    hboundary hgap

end Dev
end ConnesWeilRH
