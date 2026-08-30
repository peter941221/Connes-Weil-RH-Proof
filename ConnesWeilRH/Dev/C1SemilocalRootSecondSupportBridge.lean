/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1SemilocalDetectorSecondSupportBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace

/-!
# C1: finite-S root second-support bridge

This leaf starts the root-level part of the F1' commutator ledger.  The
detector bridge proves covariance only for `C† C`; that is insufficient for
the signed remainder `C† [C, K_S]`.  Here `C` denotes the selected compact
convolution root itself.

The first invariant is exact translation covariance.  Since each finite Euler
transport and its Hilbert adjoint are finite polynomials in logarithmic
translations, the root commutes with both.  This is algebraic infrastructure
only: no trace-class claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SemilocalRootSecondSupportBridge

open CC20Concrete
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSBandTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24RadialBoundaryPairTransport
open CCM25Concrete.SelectedCrossingOperatorBridge
open C1SemilocalFourierProjectionUnitaryBridge
open C1SemilocalHardyTitchmarshUnitarityReduction
open MeasureTheory
open scoped ENNReal FourierTransform

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The selected convolution root commutes with every logarithmic translation. -/
theorem rootConvolution_comp_translation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (b : ℝ) :
    rootConvolution owner ∘L
        (cc20GlobalLogTranslation b).toContinuousLinearMap =
      (cc20GlobalLogTranslation b).toContinuousLinearMap ∘L
        rootConvolution owner := by
  change cc20GlobalLogConvolution owner.sourceTest.involution.test ∘L
      (cc20GlobalLogTranslation b).toContinuousLinearMap =
    (cc20GlobalLogTranslation b).toContinuousLinearMap ∘L
      cc20GlobalLogConvolution owner.sourceTest.involution.test
  simpa only [neg_neg] using
    (cc20GlobalLogConvolution_comp_translation_neg_eq
      owner.sourceTest (-b))

/-- The selected convolution root commutes with one concrete Euler factor. -/
theorem rootConvolution_comp_primeEulerTransport
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) :
    rootConvolution owner ∘L
        (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap =
      (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap ∘L
        rootConvolution owner := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change rootConvolution owner (ccm24PrimeEulerTransportEquiv p u) =
    ccm24PrimeEulerTransportEquiv p (rootConvolution owner u)
  rw [ccm24PrimeEulerTransportEquiv_apply p u,
    ccm24PrimeEulerTransportEquiv_apply p (rootConvolution owner u),
    map_sub, map_smul]
  rw [show rootConvolution owner
      (cc20GlobalLogTranslation (-Real.log p) u) =
        cc20GlobalLogTranslation (-Real.log p) (rootConvolution owner u) by
    have h := congrArg
      (fun operator : Op => operator u)
      (rootConvolution_comp_translation owner (-Real.log p))
    simpa only [ContinuousLinearMap.comp_apply] using h]

/-- The selected convolution root commutes with the complete finite Euler
transport. -/
theorem rootConvolution_comp_finiteEulerTransport
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) :
    rootConvolution owner ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        rootConvolution owner := by
  induction S with
  | nil =>
      rw [ccm24FiniteEulerTransportEquiv_nil]
      apply ContinuousLinearMap.ext
      intro u
      rfl
  | cons p S ih =>
      apply ContinuousLinearMap.ext
      intro u
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      change rootConvolution owner
          (ccm24FiniteEulerTransportEquiv (p :: S) u) =
        ccm24FiniteEulerTransportEquiv (p :: S) (rootConvolution owner u)
      rw [ccm24FiniteEulerTransportEquiv_cons_apply p S u,
        ccm24FiniteEulerTransportEquiv_cons_apply p S
          (rootConvolution owner u)]
      have hp := congrArg
        (fun operator : Op =>
          operator (ccm24FiniteEulerTransportEquiv S u))
        (rootConvolution_comp_primeEulerTransport owner p)
      have hS := congrArg (fun operator : Op => operator u) ih
      simp only [ContinuousLinearMap.comp_apply] at hp hS
      change rootConvolution owner
          (ccm24PrimeEulerTransportEquiv p
            (ccm24FiniteEulerTransportEquiv S u)) =
        ccm24PrimeEulerTransportEquiv p
          (rootConvolution owner (ccm24FiniteEulerTransportEquiv S u)) at hp
      calc
        rootConvolution owner
            (ccm24PrimeEulerTransportEquiv p
              (ccm24FiniteEulerTransportEquiv S u)) =
          ccm24PrimeEulerTransportEquiv p
            (rootConvolution owner
              (ccm24FiniteEulerTransportEquiv S u)) := hp
        _ = ccm24PrimeEulerTransportEquiv p
            (ccm24FiniteEulerTransportEquiv S
              (rootConvolution owner u)) := congrArg
                (ccm24PrimeEulerTransportEquiv p) hS

/-- The Hilbert adjoint of one Euler factor also commutes with the selected
convolution root.  Unlike the detector version, this cannot be obtained merely
by taking the adjoint of a self-adjoint operator identity. -/
theorem primeEulerTransportAdjoint_comp_rootConvolution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) :
    (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap.adjoint ∘L
        rootConvolution owner =
      rootConvolution owner ∘L
        (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap.adjoint := by
  rw [ccm24PrimeEulerTransport_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_smul]
  have htranslation : rootConvolution owner
      ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap u) =
        (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
          (rootConvolution owner u) := by
    have h := congrArg
      (fun operator : Op => operator u)
      (rootConvolution_comp_translation owner (Real.log p))
    simpa only [ContinuousLinearMap.comp_apply] using h
  rw [htranslation]

/-- The Hilbert adjoint of the full finite Euler transport commutes with the
selected convolution root. -/
theorem finiteEulerTransportAdjoint_comp_rootConvolution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) :
    (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint ∘L
        rootConvolution owner =
      rootConvolution owner ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint := by
  induction S with
  | nil =>
      rw [ccm24FiniteEulerTransportEquiv_nil]
      change (ContinuousLinearMap.id ℂ finiteSCarrier).adjoint ∘L
          rootConvolution owner =
        rootConvolution owner ∘L (ContinuousLinearMap.id ℂ finiteSCarrier).adjoint
      rw [ContinuousLinearMap.adjoint_id]
      simp
  | cons p S ih =>
      rw [ccm24FiniteEulerTransport_cons_toContinuousLinearMap,
        ContinuousLinearMap.adjoint_comp]
      let Tp : Op := (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
      let TS : Op := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
      let C : Op := rootConvolution owner
      have hp : Tp.adjoint ∘L C = C ∘L Tp.adjoint := by
        dsimp only [Tp, C]
        exact primeEulerTransportAdjoint_comp_rootConvolution owner p
      have hS : TS.adjoint ∘L C = C ∘L TS.adjoint := by
        dsimp only [TS, C]
        exact ih
      change (TS.adjoint ∘L Tp.adjoint) ∘L C =
        C ∘L (TS.adjoint ∘L Tp.adjoint)
      calc
        (TS.adjoint ∘L Tp.adjoint) ∘L C =
            TS.adjoint ∘L (Tp.adjoint ∘L C) := by
              apply ContinuousLinearMap.ext
              intro u
              rfl
        _ = TS.adjoint ∘L (C ∘L Tp.adjoint) := by rw [hp]
        _ = (TS.adjoint ∘L C) ∘L Tp.adjoint := by
              apply ContinuousLinearMap.ext
              intro u
              rfl
        _ = (C ∘L TS.adjoint) ∘L Tp.adjoint := by rw [hS]
        _ = C ∘L (TS.adjoint ∘L Tp.adjoint) := by
              apply ContinuousLinearMap.ext
              intro u
              rfl

/-- Conjugating the selected convolution root by the finite-S
Hardy--Titchmarsh involution gives its exact archimedean conjugate.  The
transport disappears algebraically only because the root commutes with both
the finite Euler product and its Hilbert adjoint. -/
theorem semilocalHardyTitchmarsh_root_conjugation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) :
    (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap ∘L
        rootConvolution owner ∘L
          (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap =
      archimedeanHardyTitchmarshOperator ∘L rootConvolution owner ∘L
        archimedeanHardyTitchmarshOperator := by
  let T : Op := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
  let Ti : Op := (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap
  let Harch : Op := archimedeanHardyTitchmarshOperator
  let C : Op := rootConvolution owner
  have hfactor :
      (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap =
        (T ∘L Harch) ∘L Ti := by
    dsimp only [T, Harch, Ti, archimedeanHardyTitchmarshOperator]
    exact ccm24SemilocalHardyTitchmarsh_toContinuousLinearMap S
  have hCT : C * T = T * C := by
    dsimp only [C, T]
    change rootConvolution owner ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        rootConvolution owner
    exact rootConvolution_comp_finiteEulerTransport owner S
  have hTiT : Ti * T = 1 := by
    dsimp only [Ti, T]
    change (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (1 : Op)
    exact ccm24FiniteEulerTransport_symm_comp_toContinuousLinearMap S
  have hTTi : T * Ti = 1 := by
    dsimp only [Ti, T]
    change (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap =
      (1 : Op)
    exact ccm24FiniteEulerTransport_comp_symm_toContinuousLinearMap S
  have hHT : Harch * T = T.adjoint * Harch := by
    dsimp only [Harch, T, archimedeanHardyTitchmarshOperator]
    change (ccm24ArchimedeanHardyTitchmarsh : Op) ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint ∘L
        (ccm24ArchimedeanHardyTitchmarsh : Op)
    exact archimedeanHardyTitchmarsh_comp_finiteEulerTransport S
  have hTH : T * Harch = Harch * T.adjoint := by
    dsimp only [Harch, T, archimedeanHardyTitchmarshOperator]
    change (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        (ccm24ArchimedeanHardyTitchmarsh : Op) =
      (ccm24ArchimedeanHardyTitchmarsh : Op) ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint
    exact ccm24FiniteEulerTransport_comp_archimedeanHardyTitchmarsh S
  have hTadjC : T.adjoint * C = C * T.adjoint := by
    dsimp only [T, C]
    change (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint ∘L
        rootConvolution owner =
      rootConvolution owner ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint
    exact finiteEulerTransportAdjoint_comp_rootConvolution owner S
  have hCTAt (u : finiteSCarrier) : C (T u) = T (C u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : Op => operator u) hCT
  have hTiTAt (u : finiteSCarrier) : Ti (T u) = u := by
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
      congrArg (fun operator : Op => operator u) hTiT
  have hTTiAt (u : finiteSCarrier) : T (Ti u) = u := by
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
      congrArg (fun operator : Op => operator u) hTTi
  have hHTAt (u : finiteSCarrier) : Harch (T u) = T.adjoint (Harch u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : Op => operator u) hHT
  have hTHAt (u : finiteSCarrier) : T (Harch u) = Harch (T.adjoint u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : Op => operator u) hTH
  have hTadjCAt (u : finiteSCarrier) : T.adjoint (C u) = C (T.adjoint u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : Op => operator u) hTadjC
  have hTiCTAt (u : finiteSCarrier) : Ti (C (T u)) = C u := by
    calc
      Ti (C (T u)) = Ti (T (C u)) := congrArg Ti (hCTAt u)
      _ = C u := hTiTAt (C u)
  have hBcommAt (u : finiteSCarrier) :
      Harch (C (Harch (T u))) = T (Harch (C (Harch u))) := by
    calc
      Harch (C (Harch (T u))) =
          Harch (C (T.adjoint (Harch u))) := by
        exact congrArg (fun v => Harch (C v)) (hHTAt u)
      _ = Harch (T.adjoint (C (Harch u))) := by
        exact congrArg Harch (hTadjCAt (Harch u)).symm
      _ = T (Harch (C (Harch u))) := (hTHAt (C (Harch u))).symm
  rw [hfactor]
  apply ContinuousLinearMap.ext
  intro u
  change T (Harch (Ti (C (T (Harch (Ti u)))))) = Harch (C (Harch u))
  calc
    T (Harch (Ti (C (T (Harch (Ti u)))))) =
        T (Harch (C (Harch (Ti u)))) := by
      exact congrArg (fun v => T (Harch v)) (hTiCTAt (Harch (Ti u)))
    _ = Harch (C (Harch (T (Ti u)))) := (hBcommAt (Ti u)).symm
    _ = Harch (C (Harch u)) := by
      exact congrArg (fun v => Harch (C (Harch v))) (hTTiAt u)

/-- Reflection of the selected root is the same pointwise operation as
reflecting its involution kernel. -/
theorem reflection_involution_apply
    (g : CompactLogConvolution.CompactLogTest) (x : ℝ) :
    g.reflection.involution.test x = g.involution.test (-x) := by
  simp only [CompactLogConvolution.CompactLogTest.involution_apply,
    CompactLogConvolution.CompactLogTest.reflection_apply, neg_neg]

/-- Fourier transform of the reflected convolution root is the reflected
Fourier multiplier of the original root. -/
theorem fourier_reflection_involution_apply
    (g : CompactLogConvolution.CompactLogTest) (xi : ℝ) :
    (𝓕 g.reflection.involution.test) xi =
      (𝓕 g.involution.test) (-xi) := by
  calc
    (𝓕 g.reflection.involution.test) xi =
        𝓕 (fun x : ℝ => g.involution.test (-x)) xi := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact reflection_involution_apply g x
    _ = (𝓕 g.involution.test) (-xi) := by
      change 𝓕 ((g.involution.test : ℝ → ℂ) ∘
        LinearIsometryEquiv.neg ℝ) xi = _
      exact Real.fourier_comp_linearIsometry
        (LinearIsometryEquiv.neg ℝ)
        (g.involution.test : ℝ → ℂ) xi

/-- Conjugating the Fourier multiplier of a compact root by spectral
reflection is the multiplier of the reflected compact root. -/
theorem reflectedRootFourierMultiplier_eq_reflection_conjugation
    (g : CompactLogConvolution.CompactLogTest) :
    cc20FourierMultiplier g.reflection.involution.test =
      logSpectralReflectionOperator ∘L
        cc20FourierMultiplier g.involution.test ∘L
          logSpectralReflectionOperator := by
  apply ContinuousLinearMap.ext
  intro u
  unfold logSpectralReflectionOperator
  simp only [ContinuousLinearMap.comp_apply, cc20FourierMultiplier_apply]
  change ((𝓕 g.reflection.involution.test).toLp ⊤ • u : finiteSCarrier) =
    ccm24LogSpectralReflection
      (((𝓕 g.involution.test).toLp ⊤) • ccm24LogSpectralReflection u)
  rw [Lp.ext_iff]
  have hleft := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
    ((𝓕 g.reflection.involution.test).toLp ⊤) u
  have hleftMultiplier :=
    SchwartzMap.coeFn_toLp (𝓕 g.reflection.involution.test) ⊤
  have houter := ccm24LogSpectralReflectionEquiv_coeFn
    (((𝓕 g.involution.test).toLp ⊤) • ccm24LogSpectralReflection u)
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
  simp only [Function.comp_apply] at hinnerAt
  simp only [Function.comp_apply] at horiginalMultiplierAt
  simp only [Function.comp_apply] at hreflectionAt
  rw [hleftAt, houterAt, hinnerAt]
  simp only [Pi.smul_apply']
  rw [hleftMultiplierAt, horiginalMultiplierAt, hreflectionAt]
  simp only [smul_eq_mul, neg_neg]
  rw [fourier_reflection_involution_apply]

/-- The spectral-reflection representation of the reflected compact root. -/
noncomputable def reflectedSpectralRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Op :=
  globalLogFourierInverseOperator ∘L logSpectralReflectionOperator ∘L
    cc20FourierMultiplier owner.sourceTest.involution.test ∘L
      logSpectralReflectionOperator ∘L globalLogFourierOperator

/-- The reflected spectral root is ordinary convolution by the explicit
reflected compact root. -/
theorem reflectedSpectralRoot_eq_reflectedConvolution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    reflectedSpectralRoot owner =
      cc20GlobalLogConvolution owner.sourceTest.reflection.involution.test := by
  apply ContinuousLinearMap.ext
  intro u
  unfold reflectedSpectralRoot cc20GlobalLogConvolution
    globalLogFourierOperator globalLogFourierInverseOperator
    logSpectralReflectionOperator
  simp only [ContinuousLinearMap.comp_apply]
  have hmultiplier := congrArg
    (fun T : Op => T ((Lp.fourierTransformₗᵢ ℝ ℂ) u))
    (reflectedRootFourierMultiplier_eq_reflection_conjugation owner.sourceTest)
  simp only [ContinuousLinearMap.comp_apply,
    logSpectralReflectionOperator] at hmultiplier
  exact congrArg (Lp.fourierTransformₗᵢ ℝ ℂ).symm hmultiplier.symm

/-- The archimedean Hardy--Titchmarsh conjugate of the selected root is its
spectral reflection.  The scattering phase cancels exactly; no phase choice or
square-root extraction is used. -/
theorem archimedeanHardyTitchmarsh_root_conjugation_eq_reflectedSpectralRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    archimedeanHardyTitchmarshOperator ∘L rootConvolution owner ∘L
        archimedeanHardyTitchmarshOperator =
      reflectedSpectralRoot owner := by
  apply ContinuousLinearMap.ext
  intro u
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  unfold archimedeanHardyTitchmarshOperator rootConvolution reflectedSpectralRoot
    globalLogFourierOperator globalLogFourierInverseOperator
    logSpectralReflectionOperator
  simp only [ContinuousLinearMap.comp_apply]
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
      (ccm24ArchimedeanHardyTitchmarsh
        (cc20GlobalLogConvolution owner.sourceTest.involution.test
          (ccm24ArchimedeanHardyTitchmarsh u))) =
    (Lp.fourierTransformₗᵢ ℝ ℂ)
      ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (ccm24LogSpectralReflection
          (cc20FourierMultiplier owner.sourceTest.involution.test
            (ccm24LogSpectralReflection
              ((Lp.fourierTransformₗᵢ ℝ ℂ) u)))))
  rw [ccm24ArchimedeanHardyTitchmarsh_fourier_readback]
  rw [fourier_globalLogConvolution]
  rw [ccm24ArchimedeanHardyTitchmarsh_fourier_readback]
  rw [(Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply]
  let z := (Lp.fourierTransformₗᵢ ℝ ℂ) u
  let A := cc20FourierMultiplier owner.sourceTest.involution.test
  have hcommAt := congrArg
    (fun T : Op => T (ccm24LogSpectralReflection z))
    (archimedeanScatteringMultiplier_comp_fourierMultiplier
      owner.sourceTest.involution.test)
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

/-- The archimedean root conjugate is the explicit reflected compact root. -/
theorem archimedeanHardyTitchmarsh_root_conjugation_eq_reflectedRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    archimedeanHardyTitchmarshOperator ∘L rootConvolution owner ∘L
        archimedeanHardyTitchmarshOperator =
      cc20GlobalLogConvolution owner.sourceTest.reflection.involution.test := by
  rw [archimedeanHardyTitchmarsh_root_conjugation_eq_reflectedSpectralRoot,
    reflectedSpectralRoot_eq_reflectedConvolution]

/-- The actual finite-S Hardy--Titchmarsh conjugate of the selected root is
the explicit reflected compact convolution root. -/
theorem semilocalHardyTitchmarsh_root_conjugation_eq_reflectedRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) :
    (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap ∘L
        rootConvolution owner ∘L
          (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap =
      cc20GlobalLogConvolution owner.sourceTest.reflection.involution.test := by
  rw [semilocalHardyTitchmarsh_root_conjugation,
    archimedeanHardyTitchmarsh_root_conjugation_eq_reflectedRoot]

/-- The finite-S second-support commutator of the root is exactly the
semilocal unitary sandwich of the compact reflected-root boundary commutator.
This is the root-level counterpart of the earlier detector bridge. -/
theorem targetFourierSupport_rootCommutator_eq_reflectedRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    cc20Commutator (targetFourierSupportProjection lambda family)
        (rootConvolution owner) =
      (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap ∘L
        cc20Commutator (radialSupportProjection lambda)
          (cc20GlobalLogConvolution
            owner.sourceTest.reflection.involution.test) ∘L
          (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap := by
  let HS : Op :=
    (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap
  let E : Op := radialSupportProjection lambda
  let C : Op := rootConvolution owner
  let Q : Op := targetFourierSupportProjection lambda family
  let B : Op := cc20GlobalLogConvolution
    owner.sourceTest.reflection.involution.test
  have hQ : Q = HS * E * HS := by
    dsimp only [Q, HS, E]
    simpa only [ContinuousLinearMap.mul_def] using
      targetFourierSupportProjection_eq_unitary_conjugate lambda family
  have hHSsq : HS * HS = 1 := by
    dsimp only [HS]
    simpa only [ContinuousLinearMap.mul_def] using
      ccm24SemilocalHardyTitchmarsh_comp_self family.visiblePrimes
  have hB : HS * C * HS = B := by
    dsimp only [HS, C, B]
    simpa only [ContinuousLinearMap.mul_def] using
      semilocalHardyTitchmarsh_root_conjugation_eq_reflectedRoot owner
        family.visiblePrimes
  unfold cc20Commutator
  dsimp only [Q] at hQ
  rw [hQ]
  change (HS * E * HS) * C - C * (HS * E * HS) =
    HS * (E * B - B * E) * HS
  calc
    (HS * E * HS) * C - C * (HS * E * HS) =
        (HS * E * HS) * C * (HS * HS) -
          (HS * HS) * C * (HS * E * HS) := by
      rw [hHSsq]
      noncomm_ring
    _ = HS * (E * (HS * C * HS) - (HS * C * HS) * E) * HS := by
      noncomm_ring
    _ = HS * (E * B - B * E) * HS := by
      rw [hB]

/-- The target root second-support branch is now an explicit compact-root
boundary commutator with only bounded Euler/Hardy sandwiches around it.  This
identifies a genuine S2 subproblem; it does not falsely upgrade one
Hilbert--Schmidt boundary factor to trace class. -/
theorem targetRootSecondSupportCommutatorBranch_eq_reflectedRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    cc20SecondSupportCommutatorBranch
        (radialSupportProjection lambda)
        (targetFourierSupportProjection lambda family)
        (rootConvolution owner) =
      radialSupportProjection lambda ∘L
        (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap ∘L
          cc20Commutator (radialSupportProjection lambda)
            (cc20GlobalLogConvolution
              owner.sourceTest.reflection.involution.test) ∘L
            (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap ∘L
          radialSupportProjection lambda := by
  unfold cc20SecondSupportCommutatorBranch
  rw [targetFourierSupport_rootCommutator_eq_reflectedRoot owner lambda family]
  apply ContinuousLinearMap.ext
  intro u
  rfl

end C1SemilocalRootSecondSupportBridge
end Source
end ConnesWeilRH
