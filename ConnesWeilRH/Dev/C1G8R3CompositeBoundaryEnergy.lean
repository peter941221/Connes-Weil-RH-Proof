/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3InternalProlateGapEnergy
import ConnesWeilRH.Dev.C1G8R3BoundaryOutputFactorizationBridge
import ConnesWeilRH.Dev.ELambdaFamilyProjectorProbe
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandFirstJetTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalSupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRadialFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit

/-!
# Composite boundary OUT legs at a wider radial scale

The two OUT legs of a G8 boundary output `M ∘L J ∘L N` with a non-identity
ambient factor `M` (map 042 §4), reduced to a composite wide-radial support
fact.  With `E_λ` the radial projection at scale `λ` and `E_λ''` the radial
projection at the wider scale `λ'' = λ·e^(-s)` (`s ≥ 0`), the algebraic
identity `I - E_λ = (I - E_λ'') + (E_λ'' - E_λ)` splits the radial-boundary
leg as

    (I - E_λ) C M J   =   (I - E_λ'') C E_λ'' M J                    (A)
                        + (E_λ'' - E_λ) C E_λ'' M J                  (B)

Term (A) is the committed oriented crossing read at the scale `λ''` — a
unitary translate of the finite root window.  For term (B) the radial
difference is the translate of the interval projection
`E_λ'' - E_λ = T(-log λ) ∘L kernelIntervalProjection (-s) 0 0 ∘L T(log λ)`,
and since `C` commutes with translations the strip factors through the
compact-kernel window with output `[-s, 0]` and forced input `[-s-R, R]`,
which is Hilbert-Schmidt.  Hence both terms are square-summable GIVEN the
composite wide-radial input fact `E_λ'' M J = M J`; that support fact is the
open composite input of the brick and no instance of it is proved here.

The internal-gap leg splits through the committed prolate factor (free) and
the Hardy-Titchmarsh conjugated crossing, conditional on the corresponding
conjugated support fact.  No in-Sonin (IN) estimate is claimed; the gate,
ρ4/ρ5, C3, and RH remain open.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.CompactConvolutionSupport
open Source.CC20Concrete.ContinuousKernelHilbertSchmidt
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
open Source.CCM25Concrete.CCM24FiniteSActualBandFirstJetTrace
open Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
open Source.CCM25Concrete.CCM24FiniteSCausalSupport
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRadial
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CC20Concrete.ELambdaProjector
open scoped ENNReal InnerProduct InnerProductSpace

local notation "Carrier" => finiteSCarrier

noncomputable local instance compositeEnergySoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- A named Hilbert basis of any complete complex Hilbert space (used to
instantiate the window and strip estimates on ambient bases). -/
private noncomputable def compositeBasisIndex
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : Set G :=
  Classical.choose (exists_hilbertBasis ℂ G)

private noncomputable def compositeBasis
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : HilbertBasis (compositeBasisIndex G) ℂ G :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ G))

/-! ## The wider radial scale and the half-line difference -/

/-- The Sonin scale whose radial half-line is wider than `lambda`'s by the
logarithmic shift `s`: the support edge moves left from `log λ` to
`log λ - s`. -/
noncomputable def wideRadialScale (lambda : CCM24SoninScale) (s : ℝ) :
    CCM24SoninScale :=
  ⟨lambda.val * Real.exp (-s), mul_pos lambda.2 (Real.exp_pos (-s))⟩

theorem realLog_wideRadialScale (lambda : CCM24SoninScale) (s : ℝ) :
    Real.log (wideRadialScale lambda s) = Real.log lambda - s := by
  unfold wideRadialScale
  rw [Real.log_mul (ne_of_gt lambda.2) (Real.exp_ne_zero (-s)), Real.log_exp]
  ring

/-! A translation toward larger logarithmic coordinates shifts an upper
radial support edge to the wider scale. -/
theorem cc20GlobalLogTranslation_mem_wideRadialSupport
    (lambda : CCM24SoninScale) (b : ℝ) (hb : 0 ≤ b)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    cc20GlobalLogTranslation b u ∈
      ccm24LogRadialSupportClosedSubspace (wideRadialScale lambda b) := by
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff] at hu ⊢
  have hshift :=
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae hu
  have hlog := realLog_wideRadialScale lambda b
  filter_upwards [cc20GlobalLogTranslation_coeFn b u, hshift] with t
      htranslationAt hzeroAt
  intro ht
  rw [htranslationAt]
  apply hzeroAt
  linarith

/-! A support factor already contained in the original radial half-line is
automatically contained in every wider half-line.  This is the reusable
support consumer for composite boundary inputs; it does not assert that an
arbitrary Euler boundary factor has the premise. -/
theorem wideRadial_absorption_of_radialSupport
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    (M : Carrier →L[ℂ] Carrier)
    (hM : radialSupportProjection lambda ∘L M = M) :
    radialSupportProjection (wideRadialScale lambda s) ∘L M = M := by
  have hexp : Real.exp (-s) ≤ (1 : ℝ) :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hle : (wideRadialScale lambda s).1 ≤ lambda.1 := by
    dsimp [wideRadialScale]
    calc
      lambda.val * Real.exp (-s) ≤ lambda.val * 1 :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt lambda.2)
      _ = lambda.val := by ring
  have hproj := radialProjector_comp_of_le (wideRadialScale lambda s) hle
  apply ContinuousLinearMap.ext
  intro u
  have hMat := congrArg (fun T : Carrier →L[ℂ] Carrier => T u) hM
  have hprojAt := congrArg (fun T : Carrier →L[ℂ] Carrier => T (M u)) hproj
  simp only [ContinuousLinearMap.comp_apply] at hMat hprojAt ⊢
  calc
    radialSupportProjection (wideRadialScale lambda s) (M u) =
        radialSupportProjection (wideRadialScale lambda s)
          (radialSupportProjection lambda (M u)) := by rw [hMat]
    _ = radialSupportProjection lambda (M u) := hprojAt
    _ = M u := hMat

theorem wideRadial_absorption_of_hardyRadialSupport
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    (M : Carrier →L[ℂ] Carrier)
    (hM : radialSupportProjection lambda ∘L
        archimedeanHardyTitchmarshOperator ∘L M =
      archimedeanHardyTitchmarshOperator ∘L M) :
    radialSupportProjection (wideRadialScale lambda s) ∘L
        archimedeanHardyTitchmarshOperator ∘L M =
      archimedeanHardyTitchmarshOperator ∘L M := by
  exact wideRadial_absorption_of_radialSupport lambda s hs
    (archimedeanHardyTitchmarshOperator ∘L M) hM

theorem wideRadial_absorption_of_sourceRadialSupport
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    (M : Carrier →L[ℂ] Carrier)
    (hM : radialSupportProjection lambda ∘L M ∘L
        sourceInclusion lambda = M ∘L sourceInclusion lambda) :
    radialSupportProjection (wideRadialScale lambda s) ∘L M ∘L
        sourceInclusion lambda = M ∘L sourceInclusion lambda := by
  have hexp : Real.exp (-s) ≤ (1 : ℝ) :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hle : (wideRadialScale lambda s).1 ≤ lambda.1 := by
    dsimp [wideRadialScale]
    calc
      lambda.val * Real.exp (-s) ≤ lambda.val * 1 :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt lambda.2)
      _ = lambda.val := by ring
  have hproj := radialProjector_comp_of_le (wideRadialScale lambda s) hle
  apply ContinuousLinearMap.ext
  intro u
  have hMat := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier => T u) hM
  have hprojAt := congrArg (fun T : Carrier →L[ℂ] Carrier =>
      T ((M ∘L sourceInclusion lambda) u)) hproj
  simp only [ContinuousLinearMap.comp_apply] at hMat hprojAt ⊢
  calc
    radialSupportProjection (wideRadialScale lambda s)
        (M (sourceInclusion lambda u)) =
        radialSupportProjection (wideRadialScale lambda s)
          (radialSupportProjection lambda (M (sourceInclusion lambda u))) := by
      rw [hMat]
    _ = radialSupportProjection lambda (M (sourceInclusion lambda u)) := hprojAt
    _ = M (sourceInclusion lambda u) := hMat

theorem wideRadial_absorption_of_sourceHardyRadialSupport
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    (M : Carrier →L[ℂ] Carrier)
    (hM : radialSupportProjection lambda ∘L
        archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda =
      archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda) :
    radialSupportProjection (wideRadialScale lambda s) ∘L
        archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda =
      archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda := by
  have hexp : Real.exp (-s) ≤ (1 : ℝ) :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hle : (wideRadialScale lambda s).1 ≤ lambda.1 := by
    dsimp [wideRadialScale]
    calc
      lambda.val * Real.exp (-s) ≤ lambda.val * 1 :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt lambda.2)
      _ = lambda.val := by ring
  have hproj := radialProjector_comp_of_le (wideRadialScale lambda s) hle
  apply ContinuousLinearMap.ext
  intro u
  have hMat := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier => T u) hM
  have hprojAt := congrArg (fun T : Carrier →L[ℂ] Carrier =>
      T ((archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda) u))
    hproj
  simp only [ContinuousLinearMap.comp_apply] at hMat hprojAt ⊢
  calc
    radialSupportProjection (wideRadialScale lambda s)
        (archimedeanHardyTitchmarshOperator
          (M (sourceInclusion lambda u))) =
        radialSupportProjection (wideRadialScale lambda s)
          (radialSupportProjection lambda
            (archimedeanHardyTitchmarshOperator
              (M (sourceInclusion lambda u)))) := by
      rw [hMat]
    _ = radialSupportProjection lambda
        (archimedeanHardyTitchmarshOperator
          (M (sourceInclusion lambda u))) := hprojAt
    _ = archimedeanHardyTitchmarshOperator
        (M (sourceInclusion lambda u)) := hMat

/-! The genuine forward one-prime Euler transport supplies the original-scale
radial premise needed by the wider-scale consumer.  This is the first
concrete instance of `hwide`: the source inclusion is radial and the forward
transport is causal, so no wider support theorem is needed for this factor. -/
theorem normalizedPrimeEulerFrameTransport_sourceRadialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L
        normalizedPrimeEulerFrameTransport p ∘L sourceInclusion lambda =
      normalizedPrimeEulerFrameTransport p ∘L sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hsource := sourceInclusion_mem_radialSupport lambda u
  have htransport := ccm24PrimeEulerTransportEquiv_mem_logRadialSupport
    lambda p hsource
  have hscaled :
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
          ccm24PrimeEulerTransportEquiv p (sourceInclusion lambda u) ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
    (ccm24LogRadialSupportClosedSubspace lambda).smul_mem _ htransport
  have hfixed :=
    (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2 hscaled
  simpa only [normalizedPrimeEulerFrameTransport,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] using hfixed

theorem normalizedPrimeEulerFrameTransport_sourceWideRadialSupport
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    (p : CCM24VisiblePrime) :
    radialSupportProjection (wideRadialScale lambda s) ∘L
        normalizedPrimeEulerFrameTransport p ∘L sourceInclusion lambda =
      normalizedPrimeEulerFrameTransport p ∘L sourceInclusion lambda := by
  exact wideRadial_absorption_of_sourceRadialSupport lambda s hs
    (normalizedPrimeEulerFrameTransport p)
    (normalizedPrimeEulerFrameTransport_sourceRadialSupport lambda p)

/-! The same source-column support statement holds for the complete finite
forward Euler transport used by the arithmetic family. -/
theorem finiteEulerTransport_sourceRadialSupport
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialSupportProjection lambda ∘L
        finiteEulerTransportOperator family ∘L sourceInclusion lambda =
      finiteEulerTransportOperator family ∘L sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have htransport :=
    congrArg (fun T : Carrier →L[ℂ] Carrier => T
      (sourceInclusion lambda u))
      (radialSupportProjection_comp_transport_comp_self lambda family)
  have hsource := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier => T u)
    (radialSupportProjection_comp_sourceInclusion lambda)
  simp only [ContinuousLinearMap.comp_apply] at htransport hsource ⊢
  rw [← hsource]
  exact htransport

theorem finiteEulerTransport_sourceWideRadialSupport
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    (family : FinitePrimePowerFamily) :
    radialSupportProjection (wideRadialScale lambda s) ∘L
        finiteEulerTransportOperator family ∘L sourceInclusion lambda =
      finiteEulerTransportOperator family ∘L sourceInclusion lambda := by
  exact wideRadial_absorption_of_sourceRadialSupport lambda s hs
    (finiteEulerTransportOperator family)
    (finiteEulerTransport_sourceRadialSupport lambda family)

/-! The adjoint one-prime transport has an exact radial leakage channel.  The
identity is the operator-level bridge from the actual Schur boundary head to
the already owned `primeEulerRadialBoundaryStep`; it makes no estimate. -/
theorem normalizedPrimeEulerFrameTransport_adjoint_radialLeakage
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialComplement lambda ∘L
        ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p) ∘L
          radialSupportProjection lambda =
      (-((ccm24PrimeEulerCoefficient p : ℂ) *
          (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹)) •
        primeEulerRadialBoundaryStep lambda p := by
  apply ContinuousLinearMap.ext
  intro x
  have hfixed : radialSupportProjection lambda
      (radialSupportProjection lambda x) =
        radialSupportProjection lambda x := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.starProjection_apply_mem _ _)
  have hzero : radialComplement lambda
      (radialSupportProjection lambda x) = 0 :=
    radialComplement_apply_eq_zero_of_fixed lambda hfixed
  rw [normalizedPrimeEulerFrameTransport_adjoint_eq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    radialComplement, primeEulerRadialBoundaryStep,
    map_sub, map_smul, hfixed, hzero, zero_sub]
  module

theorem primeEulerAmbientLossFactor_adjoint_radialLeakage
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialComplement lambda ∘L
        ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) ∘L
          radialSupportProjection lambda =
      (primeEulerAmbientLossScale p : ℂ) •
        primeEulerRadialBoundaryStep lambda p := by
  apply ContinuousLinearMap.ext
  intro x
  have hfixed : radialSupportProjection lambda
      (radialSupportProjection lambda x) =
        radialSupportProjection lambda x := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.starProjection_apply_mem _ _)
  have hfactor := DFunLike.congr_fun
    (primeEulerAmbientLossFactor_adjoint_comp_radialSupport lambda p) x
  have hcore := radialComplement_antiresonantCore_apply_of_fixed
    lambda p hfixed
  have hboundary := DFunLike.congr_fun
    (primeEulerRadialBoundaryStep_comp_radialSupportProjection lambda p) x
  simp only [ContinuousLinearMap.comp_apply] at hboundary
  change radialComplement lambda
      (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
        (radialSupportProjection lambda x)) =
    (primeEulerAmbientLossScale p : ℂ) •
      primeEulerRadialBoundaryStep lambda p x
  have hfactor' :
      ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
          (radialSupportProjection lambda x) =
        (primeEulerAmbientLossScale p : ℂ) •
          primeEulerAntiresonantCore p (radialSupportProjection lambda x) := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply] using hfactor
  rw [hfactor', map_smul, hcore, hboundary]

theorem suffixEulerFrameSchurStep_oldFrame_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame =
      (suffixEulerFrameSchurStep lambda p S).oldFrame := by
  apply ContinuousLinearMap.ext
  intro x
  apply (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
  simpa only [suffixEulerFrameSchurStep, oldSuffixFrame] using
    (newSuffixFrame_mem lambda (p :: S) x).1

theorem suffixEulerFrameAmbientLossColumn_wideRadialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    radialSupportProjection (wideRadialScale lambda (Real.log p)) ∘L
        suffixEulerFrameAmbientLossColumn lambda p S =
      suffixEulerFrameAmbientLossColumn lambda p S := by
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.le)
  have hle : (wideRadialScale lambda (Real.log p)).1 ≤ lambda.1 := by
    dsimp [wideRadialScale]
    calc
      lambda.val * Real.exp (-Real.log p) ≤ lambda.val * 1 := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by linarith)) (le_of_lt lambda.2)
      _ = lambda.val := by ring
  have hproj := radialProjector_comp_of_le
    (wideRadialScale lambda (Real.log p)) hle
  apply ContinuousLinearMap.ext
  intro x
  have hOld := suffixEulerFrameSchurStep_oldFrame_radialSupport lambda p S
  have hOldPoint := DFunLike.congr_fun hOld x
  simp only [ContinuousLinearMap.comp_apply] at hOldPoint
  have hOldMem : (suffixEulerFrameSchurStep lambda p S).oldFrame x ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).1 hOldPoint
  have hOldWide : (suffixEulerFrameSchurStep lambda p S).oldFrame x ∈
      ccm24LogRadialSupportClosedSubspace
        (wideRadialScale lambda (Real.log p)) := by
    apply (ccm24LogRadialSupportProjection_eq_self_iff
      (wideRadialScale lambda (Real.log p)) _).1
    have hprojPoint := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
        T ((suffixEulerFrameSchurStep lambda p S).oldFrame x)) hproj
    simp only [ContinuousLinearMap.comp_apply] at hprojPoint
    calc
      radialSupportProjection (wideRadialScale lambda (Real.log p))
          ((suffixEulerFrameSchurStep lambda p S).oldFrame x) =
          radialSupportProjection (wideRadialScale lambda (Real.log p))
            (radialSupportProjection lambda
              ((suffixEulerFrameSchurStep lambda p S).oldFrame x)) := by
            rw [hOldPoint]
      _ = radialSupportProjection lambda
          ((suffixEulerFrameSchurStep lambda p S).oldFrame x) := hprojPoint
      _ = (suffixEulerFrameSchurStep lambda p S).oldFrame x := hOldPoint
  have htranslated := cc20GlobalLogTranslation_mem_wideRadialSupport
    lambda (Real.log p) hlogp hOldMem
  rw [suffixEulerFrameAmbientLossColumn,
    primeEulerAmbientLossFactor_adjoint_eq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  apply (ccm24LogRadialSupportProjection_eq_self_iff
    (wideRadialScale lambda (Real.log p)) _).2
  exact (ccm24LogRadialSupportClosedSubspace
    (wideRadialScale lambda (Real.log p))).smul_mem _
    ((ccm24LogRadialSupportClosedSubspace
      (wideRadialScale lambda (Real.log p))).add_mem hOldWide htranslated)

/-! The preceding global identity now reaches the actual Schur column.  The
old suffix frame is itself radially supported, so the radial complement sees
exactly the same boundary step after the frame pullback. -/
theorem suffixEulerFrameAmbientLossColumn_radialLeakage
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    radialComplement lambda ∘L
        suffixEulerFrameAmbientLossColumn lambda p S =
      (primeEulerAmbientLossScale p : ℂ) •
        (primeEulerRadialBoundaryStep lambda p ∘L
          (suffixEulerFrameSchurStep lambda p S).oldFrame) := by
  have hold := suffixEulerFrameSchurStep_oldFrame_radialSupport lambda p S
  rw [suffixEulerFrameAmbientLossColumn]
  calc
    radialComplement lambda ∘L
          ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame =
      (radialComplement lambda ∘L
          ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) ∘L
          radialSupportProjection lambda) ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame := by
      apply ContinuousLinearMap.ext
      intro x
      have hhold := DFunLike.congr_fun hold x
      simp only [ContinuousLinearMap.comp_apply] at hhold ⊢
      rw [hhold]
    _ = ((primeEulerAmbientLossScale p : ℂ) •
          primeEulerRadialBoundaryStep lambda p) ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame := by
      rw [primeEulerAmbientLossFactor_adjoint_radialLeakage]
    _ = (primeEulerAmbientLossScale p : ℂ) •
        (primeEulerRadialBoundaryStep lambda p ∘L
          (suffixEulerFrameSchurStep lambda p S).oldFrame) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, map_smul]

/-- Membership in the positive half-line. -/
theorem mem_cc20PositiveHalfLine_iff (x : ℝ) :
    x ∈ cc20PositiveHalfLine ↔ 0 ≤ x := by
  unfold cc20PositiveHalfLine
  exact Set.mem_Ici

/-- The conjugated half-line projection minus the half-line projection is the
interval projection on `[-s, 0]` for `s ≥ 0`. -/
theorem halfLineConjugate_sub_eq_intervalProjection
    (s : ℝ) (hs : 0 ≤ s) :
    (cc20GlobalLogTranslation s).toContinuousLinearMap ∘L
        cc20PositiveHalfLineProjection ∘L
          (cc20GlobalLogTranslation (-s)).toContinuousLinearMap -
      cc20PositiveHalfLineProjection =
      kernelIntervalProjection (-s) 0 0 := by
  rw [sub_eq_iff_eq_add]
  apply ContinuousLinearMap.ext
  intro u
  have houter :
      ((cc20GlobalLogTranslation s).toContinuousLinearMap ∘L
          cc20PositiveHalfLineProjection ∘L
            (cc20GlobalLogTranslation (-s)).toContinuousLinearMap) u =
        cc20GlobalLogTranslation s
          (cc20PositiveHalfLineProjection
            ((cc20GlobalLogTranslation (-s)).toContinuousLinearMap u)) := rfl
  rw [houter, Lp.ext_iff, ContinuousLinearMap.add_apply]
  have hchain := cc20GlobalLogTranslation_coeFn s
    (cc20PositiveHalfLineProjection
      ((cc20GlobalLogTranslation (-s)).toContinuousLinearMap u))
  have hinner := cc20PositiveHalfLineProjection_coeFn
    ((cc20GlobalLogTranslation (-s)).toContinuousLinearMap u)
  have hshiftInner :=
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae_eq hinner
  have htransInner :=
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae_eq
      (cc20GlobalLogTranslation_coeFn (-s) u)
  have hpos := cc20PositiveHalfLineProjection_coeFn u
  have hright := kernelIntervalProjection_coeFn (-s) 0 0 u
  have hadd := Lp.coeFn_add (kernelIntervalProjection (-s) 0 0 u)
    (cc20PositiveHalfLineProjection u)
  filter_upwards [hchain, hadd, hshiftInner, htransInner, hpos, hright,
    MeasureTheory.volume.ae_ne (0 : ℝ)] with
    t hchainAt haddAt hshiftAt htransAt hposAt hrightAt ht0
  simp only [Function.comp_apply] at hshiftAt htransAt
  rw [haddAt]
  simp only [Pi.add_apply]
  rw [hchainAt, hrightAt, hposAt, hshiftAt]
  have hcoe : ∀ (b : ℝ) (w : cc20GlobalLogCrossingL2) (r : ℝ),
      ((cc20GlobalLogTranslation b).toContinuousLinearMap w : ℝ → ℂ) r =
        (cc20GlobalLogTranslation b w : ℝ → ℂ) r := fun b w r => rfl
  simp only [sub_zero, zero_add]
  by_cases h0 : (0:ℝ) ≤ t
  · rw [Set.indicator_of_mem ((mem_cc20PositiveHalfLine_iff (t + s)).2
        (show (0:ℝ) ≤ t + s by linarith)),
      Set.indicator_of_notMem (show (t:ℝ) ∉ Set.Icc (-s) 0 from by
        intro hm
        exact absurd hm.2 (by
          rcases lt_or_gt_of_ne ht0 with hlt | hgt
          · exact absurd hlt (by linarith)
          · linarith)),
      Set.indicator_of_mem ((mem_cc20PositiveHalfLine_iff t).2 h0)]
    simp only [hcoe (-s) u (t + s), htransAt, add_assoc, add_neg_cancel,
      add_zero, zero_add]
  · by_cases hms : (0:ℝ) ≤ t + s
    · rw [Set.indicator_of_mem ((mem_cc20PositiveHalfLine_iff (t + s)).2 hms),
        Set.indicator_of_mem (show (t:ℝ) ∈ Set.Icc (-s) 0 from by
          constructor <;> linarith),
        Set.indicator_of_notMem (show (t:ℝ) ∉ cc20PositiveHalfLine from by
          intro hm
          exact absurd ((mem_cc20PositiveHalfLine_iff t).1 hm) (by linarith))]
      simp only [hcoe (-s) u (t + s), htransAt, add_assoc, add_neg_cancel,
        add_zero, zero_add]
    · rw [Set.indicator_of_notMem (show (t:ℝ) + s ∉ cc20PositiveHalfLine from by
          intro hm
          exact absurd ((mem_cc20PositiveHalfLine_iff (t + s)).1 hm)
            (by linarith)),
        Set.indicator_of_notMem (show (t:ℝ) ∉ Set.Icc (-s) 0 from by
          intro hm; exact absurd hm.1 (by linarith)),
        Set.indicator_of_notMem (show (t:ℝ) ∉ cc20PositiveHalfLine from by
          intro hm
          exact absurd ((mem_cc20PositiveHalfLine_iff t).1 hm) (by linarith))]
      simp only [hcoe (-s) u (t + s), htransAt, add_assoc, add_neg_cancel,
        add_zero, zero_add]

/-- The radial difference between the wider scale and `lambda` is the unitary
translate of the interval projection on `[-s, 0]`. -/
theorem radialProjection_sub_eq_translatedInterval
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s) :
    radialSupportProjection (wideRadialScale lambda s) -
        radialSupportProjection lambda =
      (cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap ∘L
        kernelIntervalProjection (-s) 0 0 ∘L
          (cc20GlobalLogTranslation
            (Real.log lambda)).toContinuousLinearMap := by
  have hE := radialSupportProjection_eq_translation_conjugation lambda
  have hEw := radialSupportProjection_eq_translation_conjugation
    (wideRadialScale lambda s)
  have hlog := realLog_wideRadialScale lambda s
  have hTminus :
      (cc20GlobalLogTranslation
          (-(Real.log (wideRadialScale lambda s)))).toContinuousLinearMap =
      (cc20GlobalLogTranslation s).toContinuousLinearMap ∘L
        (cc20GlobalLogTranslation
          (-(Real.log lambda))).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    rw [hlog, show (-(Real.log lambda - s):ℝ) = s + -(Real.log lambda) from by
      ring]
    simpa only [ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply] using
      (cc20GlobalLogTranslation_add_apply s (-(Real.log lambda)) v).symm
  have hTplus :
      (cc20GlobalLogTranslation
          (Real.log (wideRadialScale lambda s))).toContinuousLinearMap =
      (cc20GlobalLogTranslation (-s)).toContinuousLinearMap ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    rw [hlog, show (Real.log lambda - s:ℝ) = -s + Real.log lambda from by ring]
    simpa only [ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply] using
      (cc20GlobalLogTranslation_add_apply (-s) (Real.log lambda) v).symm
  rw [hEw, hE, hTminus, hTplus]
  apply ContinuousLinearMap.ext
  intro u
  have hhalfAt := congrArg
    (fun T : Carrier →L[ℂ] Carrier =>
      T ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap u))
    (halfLineConjugate_sub_eq_intervalProjection s hs)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply] at hhalfAt
  have hshiftPt :
      (cc20GlobalLogTranslation s).toContinuousLinearMap
          ((cc20GlobalLogTranslation
              (-(Real.log lambda))).toContinuousLinearMap
            (cc20PositiveHalfLineProjection
              ((cc20GlobalLogTranslation (-s)).toContinuousLinearMap
                ((cc20GlobalLogTranslation
                    (Real.log lambda)).toContinuousLinearMap u)))) =
      (cc20GlobalLogTranslation
          (-(Real.log lambda))).toContinuousLinearMap
        ((cc20GlobalLogTranslation s).toContinuousLinearMap
          (cc20PositiveHalfLineProjection
            ((cc20GlobalLogTranslation (-s)).toContinuousLinearMap
              ((cc20GlobalLogTranslation
                  (Real.log lambda)).toContinuousLinearMap u)))) := by
    have hcoe : ∀ (b : ℝ) (w : Carrier),
        (cc20GlobalLogTranslation b).toContinuousLinearMap w =
          cc20GlobalLogTranslation b w := fun b w => rfl
    rw [hcoe s, hcoe (-(Real.log lambda)), hcoe (-(Real.log lambda)), hcoe s,
      cc20GlobalLogTranslation_add_apply s (-(Real.log lambda)) _,
      show (s + -(Real.log lambda):ℝ) = -(Real.log lambda) + s from by ring,
      cc20GlobalLogTranslation_add_apply (-(Real.log lambda)) s _]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply]
  rw [← hhalfAt, map_sub, hshiftPt]

/-! ## The composite strip window -/

/-- The composite strip operator: the compact root kernel on the output
window `[-s, 0]` with forced input window `[-s-R, R]`, zero-extended. -/
noncomputable def compositeStripWindowOperator
    (owner : SelectedWeilSquareOwner) (s : ℝ) : Carrier →L[ℂ] Carrier :=
  kernelIntervalL2ZeroExtension (-s) 0 0 ∘L
    (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (CompactInputInterval
        (-(selectedRootSupportRadius owner))
        (selectedRootSupportRadius owner) (-s) 0))
      (volume : Measure (CompactOutputInterval (-s) 0))
      (compactOutputRootKernel owner.sourceTest
        (-(selectedRootSupportRadius owner))
        (selectedRootSupportRadius owner) (-s) 0)) ∘L
    globalL2ToKernelInterval
      ((-s) - selectedRootSupportRadius owner)
      (0 + selectedRootSupportRadius owner) 0

/-- The composite strip operator has square-summable columns on any named
ambient basis: the kernel is continuous on the compact strip. -/
theorem compositeStripWindowOperator_basis_normSq_summable
    (owner : SelectedWeilSquareOwner) (s : ℝ)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure
        (CompactInputInterval
          (-(selectedRootSupportRadius owner))
          (selectedRootSupportRadius owner) (-s) 0))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (CompactOutputInterval (-s) 0))))
    (globalBasis : HilbertBasis ν ℂ Carrier) :
    Summable fun i : ν =>
      ‖compositeStripWindowOperator owner s (globalBasis i)‖ ^ 2 := by
  let radius := selectedRootSupportRadius owner
  let kernel := compactOutputRootKernel owner.sourceTest (-radius) radius
    (-s) 0
  let kernelOperator := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (CompactInputInterval (-radius) radius (-s) 0))
    (volume : Measure (CompactOutputInterval (-s) 0)) kernel
  have hkernel : Summable fun i : κ =>
      ‖kernelOperator (inputBasis i)‖ ^ 2 := by
    exact ContinuousKernelHilbertSchmidt.basis_normSq_summable
      (volume : Measure (CompactInputInterval (-radius) radius (-s) 0))
      (volume : Measure (CompactOutputInterval (-s) 0)) kernel inputBasis
  have hrestricted : Summable fun i : ν =>
      ‖(kernelOperator ∘L globalL2ToKernelInterval
          ((-s) - radius) (0 + radius) 0) (globalBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp inputBasis outputBasis
      globalBasis kernelOperator
      (globalL2ToKernelInterval ((-s) - radius) (0 + radius) 0) hkernel
  have hextended : Summable fun i : ν =>
      ‖(kernelIntervalL2ZeroExtension (-s) 0 0 ∘L
          (kernelOperator ∘L globalL2ToKernelInterval
            ((-s) - radius) (0 + radius) 0)) (globalBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp globalBasis
      (kernelOperator ∘L globalL2ToKernelInterval
        ((-s) - radius) (0 + radius) 0)
      (kernelIntervalL2ZeroExtension (-s) 0 0) hrestricted
  simpa only [radius, kernel, kernelOperator,
    compositeStripWindowOperator, ContinuousLinearMap.comp_assoc] using
    hextended

/-! ## The composite radial-boundary leg (B3) -/

set_option maxHeartbeats 1000000 in
-- the composite operator identities normalize deep ∘L chains pointwise,
-- so the kernel defeq pass over the assembled proof term needs the budget
/-- The radial-boundary OUT leg of a composed boundary output
`(I - E_λ) C M J N` is square-summable GIVEN the composite wide-radial input
fact `E_λ'' M J = M J` at the wider scale `λ'' = λ·e^(-s)`.  The proof splits
`I - E_λ = (I - E_λ'') + (E_λ'' - E_λ)`; both terms are square-summable
through committed compact-window mechanisms.  The support fact `hwide` itself
stays open. -/
theorem compositeRadialLeg_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) (s : ℝ)
    (hs : 0 ≤ s)
    (M : Carrier →L[ℂ] Carrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hwide : radialSupportProjection (wideRadialScale lambda s) ∘L M ∘L
        sourceInclusion lambda = M ∘L sourceInclusion lambda) :
    Summable fun i : ρ =>
      ‖(((ContinuousLinearMap.id ℂ Carrier -
            radialSupportProjection lambda) ∘L rootConvolution owner ∘L M ∘L
          sourceInclusion lambda) ∘L N) (sourceBasis i)‖ ^ 2 := by
  let radius := selectedRootSupportRadius owner
  let E := radialSupportProjection lambda
  let E'' := radialSupportProjection (wideRadialScale lambda s)
  let C := rootConvolution owner
  let J := sourceInclusion lambda
  let plus := (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
  let minus :=
    (cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap
  let plus'' := (cc20GlobalLogTranslation
    (Real.log (wideRadialScale lambda s))).toContinuousLinearMap
  let minus'' := (cc20GlobalLogTranslation
    (-(Real.log (wideRadialScale lambda s)))).toContinuousLinearMap
  let globalBasis := compositeBasis Carrier
  let inputBasis := compositeBasis
    (Lp ℂ 2 (volume : Measure
      (CompactInputInterval (-radius) radius (-radius) 0)))
  let outputBasis := compositeBasis
    (Lp ℂ 2 (volume : Measure (CompactOutputInterval (-radius) 0)))
  let stripInputBasis := compositeBasis
    (Lp ℂ 2 (volume : Measure
      (CompactInputInterval (-radius) radius (-s) 0)))
  let stripOutputBasis := compositeBasis
    (Lp ℂ 2 (volume : Measure (CompactOutputInterval (-s) 0)))
  have hMJNop : (E'' ∘L M ∘L J ∘L N) = (M ∘L J ∘L N) := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
      T (N v)) hwide
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hMJNpt : ∀ v : sourceSoninCarrier lambda,
      E'' (M (J (N v))) = M (J (N v)) := by
    intro v
    have h := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
      T (N v)) hwide
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hcommute'' : C ∘L minus'' = minus'' ∘L C := by
    change (cc20GlobalLogConvolution
        owner.sourceTest.involution.test).comp
      (cc20GlobalLogTranslation
        (-(Real.log (wideRadialScale lambda s)))).toContinuousLinearMap = _
    exact cc20GlobalLogConvolution_comp_translation_neg_eq owner.sourceTest
      (Real.log (wideRadialScale lambda s))
  have hcommutePlus : plus ∘L C = C ∘L plus := by
    have h := cc20GlobalLogConvolution_comp_translation_neg_eq owner.sourceTest
      (-(Real.log lambda))
    simpa only [neg_neg] using h.symm
  have hcrossUnfolded :
      ((ContinuousLinearMap.id ℂ Carrier - E'') ∘L C ∘L E'') =
      minus'' ∘L selectedRootBoundaryWindowOperator owner ∘L plus'' := by
    change ((ContinuousLinearMap.id ℂ Carrier -
        ccm24LogRadialSupportProjection (wideRadialScale lambda s)) ∘L
      rootConvolution owner ∘L
      ccm24LogRadialSupportProjection (wideRadialScale lambda s)) = _
    rw [ccm24RadialOrientedCrossing_eq_translation_conjugation
      (wideRadialScale lambda s) (rootConvolution owner) hcommute'']
    rw [← selectedRoot_zeroBoundaryCrossing_eq_finiteWindow owner]
  have hcrossOp :
      (((ContinuousLinearMap.id ℂ Carrier - E'') ∘L C ∘L M ∘L J) ∘L N) =
      minus'' ∘L selectedRootBoundaryWindowOperator owner ∘L
        (plus'' ∘L M ∘L J ∘L N) := by
    apply ContinuousLinearMap.ext
    intro v
    have hinner := congrArg (fun T : Carrier →L[ℂ] Carrier =>
      T ((M ∘L J) (N v))) hcrossUnfolded
    simp only [ContinuousLinearMap.comp_apply] at hinner ⊢
    rw [hMJNpt v] at hinner
    exact hinner
  have hprojEq : kernelIntervalProjection (-s) 0 0 =
      kernelIntervalL2ZeroExtension (-s) 0 0 ∘L
        globalL2ToKernelInterval (-s) 0 0 := by
    change (kernelIntervalL2ZeroExtension (-s) 0 0).comp
      (kernelIntervalL2ZeroExtension (-s) 0 0).adjoint = _
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval,
      ContinuousLinearMap.adjoint_adjoint]
  have hfactor : globalL2ToKernelInterval (-s) 0 0 ∘L C =
      (ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (CompactInputInterval (-radius) radius (-s) 0))
        (volume : Measure (CompactOutputInterval (-s) 0))
        (compactOutputRootKernel owner.sourceTest (-radius) radius (-s) 0)) ∘L
      globalL2ToKernelInterval ((-s) - radius) (0 + radius) 0 := by
    calc globalL2ToKernelInterval (-s) 0 0 ∘L C
        = globalL2ToKernelInterval (-s) 0 0 ∘L
            cc20GlobalLogConvolution owner.sourceTest.involution.test := rfl
      _ = compactOutputRootFactor owner.sourceTest (-radius) radius (-s) 0 :=
            (compactOutputRootFactor_eq_globalConvolution owner.sourceTest
              (-radius) radius (-s) 0
              (selectedRoot_sourceTest_support_subset owner)).symm
      _ = _ := rfl
  have hIprojC : kernelIntervalProjection (-s) 0 0 ∘L C =
      kernelIntervalL2ZeroExtension (-s) 0 0 ∘L
        (ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (CompactInputInterval (-radius) radius (-s) 0))
          (volume : Measure (CompactOutputInterval (-s) 0))
          (compactOutputRootKernel owner.sourceTest (-radius) radius (-s) 0)) ∘L
        globalL2ToKernelInterval ((-s) - radius) (0 + radius) 0 := by
    rw [hprojEq, ContinuousLinearMap.comp_assoc, hfactor]
  have hStripUnfolded : ((E'' - E) ∘L C ∘L E'') =
      minus ∘L compositeStripWindowOperator owner s ∘L (plus ∘L E'') := by
    apply ContinuousLinearMap.ext
    intro u
    have hwrapped := congrArg
      (fun T : Carrier →L[ℂ] Carrier =>
        T (rootConvolution owner (E'' u)))
      (radialProjection_sub_eq_translatedInterval lambda s hs)
    have hstep1 := congrArg
      (fun T : Carrier →L[ℂ] Carrier => T (E'' u)) hcommutePlus
    have hIprojCat := congrArg
      (fun T : Carrier →L[ℂ] Carrier =>
        T (plus (E'' u))) hIprojC
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply] at hwrapped
    simp only [ContinuousLinearMap.comp_apply] at hstep1 hIprojCat
    simp only [compositeStripWindowOperator, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply]
    rw [hwrapped, hstep1, hIprojCat]
  have hStripOpN :
      (((E'' - E) ∘L C ∘L M ∘L J) ∘L N) =
      minus ∘L compositeStripWindowOperator owner s ∘L
        (plus ∘L M ∘L J ∘L N) := by
    apply ContinuousLinearMap.ext
    intro v
    have hinner := congrArg (fun T : Carrier →L[ℂ] Carrier =>
      T ((M ∘L J) (N v))) hStripUnfolded
    simp only [ContinuousLinearMap.comp_apply] at hinner ⊢
    rw [hMJNpt v] at hinner
    exact hinner
  have hIDE : (ContinuousLinearMap.id ℂ Carrier - E) =
      (ContinuousLinearMap.id ℂ Carrier - E'') + (E'' - E) := by
    abel
  have hwindowHS := selectedRootBoundaryWindowOperator_basis_normSq_summable
    owner inputBasis outputBasis globalBasis
  have hstripHS := compositeStripWindowOperator_basis_normSq_summable
    owner s stripInputBasis stripOutputBasis globalBasis
  have hA0 : Summable fun i : ρ =>
      ‖(minus'' ∘L selectedRootBoundaryWindowOperator owner ∘L
        (plus'' ∘L M ∘L J ∘L N)) (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_postcomp sourceBasis
      (selectedRootBoundaryWindowOperator owner ∘L
        (plus'' ∘L M ∘L J ∘L N)) minus''
      (PositiveTrace.summable_normSq_precomp globalBasis globalBasis
        sourceBasis (selectedRootBoundaryWindowOperator owner)
        (plus'' ∘L M ∘L J ∘L N) hwindowHS)
  have hA : Summable fun i : ρ =>
      ‖(((ContinuousLinearMap.id ℂ Carrier - E'') ∘L C ∘L M ∘L
          J) ∘L N) (sourceBasis i)‖ ^ 2 := by
    refine hA0.congr ?_
    intro i
    rw [congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
      T (sourceBasis i)) hcrossOp]
  have hB0 : Summable fun i : ρ =>
      ‖(minus ∘L compositeStripWindowOperator owner s ∘L
        (plus ∘L M ∘L J ∘L N)) (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_postcomp sourceBasis
      (compositeStripWindowOperator owner s ∘L
        (plus ∘L M ∘L J ∘L N)) minus
      (PositiveTrace.summable_normSq_precomp globalBasis globalBasis
        sourceBasis (compositeStripWindowOperator owner s)
        (plus ∘L M ∘L J ∘L N) hstripHS)
  have hB : Summable fun i : ρ =>
      ‖(((E'' - E) ∘L C ∘L M ∘L J) ∘L N) (sourceBasis i)‖ ^ 2 := by
    refine hB0.congr ?_
    intro i
    rw [congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
      T (sourceBasis i)) hStripOpN]
  have hOp : (((ContinuousLinearMap.id ℂ Carrier - E) ∘L C ∘L M ∘L J) ∘L N) =
      (((ContinuousLinearMap.id ℂ Carrier - E'') ∘L C ∘L M ∘L J) ∘L N) +
      (((E'' - E) ∘L C ∘L M ∘L J) ∘L N) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply]
    rw [hIDE, ContinuousLinearMap.add_apply]
  have hcombined := PositiveTrace.summable_normSq_add sourceBasis
    (((ContinuousLinearMap.id ℂ Carrier - E'') ∘L C ∘L M ∘L J) ∘L N)
    (((E'' - E) ∘L C ∘L M ∘L J) ∘L N) hA hB
  refine hcombined.congr ?_
  intro i
  rw [congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
    T (sourceBasis i)) hOp]

/-! ## The composite internal-gap leg (B4) -/

/- The deep operator reassociation used by B4 is kept as a separate
   declaration.  This prevents the final summability theorem from making the
   kernel re-check the entire projection and Hardy conjugation chain. -/
theorem compositeGapLeg_secondIdentity
    (lambda : CCM24SoninScale)
    (B E Q C H Crefl : Carrier →L[ℂ] Carrier)
    (M : Carrier →L[ℂ] Carrier)
    (J : sourceSoninCarrier lambda →L[ℂ] Carrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (hBComplement : B ∘L (ContinuousLinearMap.id ℂ Carrier - Q) =
      E ∘L (ContinuousLinearMap.id ℂ Carrier - Q))
    (hIQC : (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C =
      H ∘L (ContinuousLinearMap.id ℂ Carrier - E) ∘L Crefl ∘L H) :
    E ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L
        (M ∘L J ∘L N) =
      ((B ∘L H) ∘L
        ((ContinuousLinearMap.id ℂ Carrier - E) ∘L Crefl ∘L H ∘L M ∘L J ∘L
          N)) := by
  calc
    E ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L (M ∘L J ∘L N)
        = (E ∘L (ContinuousLinearMap.id ℂ Carrier - Q)) ∘L C ∘L
            (M ∘L J ∘L N) := rfl
    _ = (B ∘L (ContinuousLinearMap.id ℂ Carrier - Q)) ∘L C ∘L
            (M ∘L J ∘L N) := by rw [hBComplement]
    _ = (B ∘L ((ContinuousLinearMap.id ℂ Carrier - Q) ∘L C)) ∘L
            (M ∘L J ∘L N) := rfl
    _ = (B ∘L (H ∘L (ContinuousLinearMap.id ℂ Carrier - E) ∘L Crefl ∘L
              H)) ∘L (M ∘L J ∘L N) := by rw [hIQC]
    _ = (B ∘L H) ∘L ((ContinuousLinearMap.id ℂ Carrier - E) ∘L Crefl ∘L
          H ∘L (M ∘L J ∘L N)) := rfl

theorem compositeGapLeg_hIQC
    (E Q C H Crefl : Carrier →L[ℂ] Carrier)
    (hHH : H ∘L H = ContinuousLinearMap.id ℂ Carrier)
    (hHCH : H ∘L C = Crefl ∘L H)
    (hleft : H ∘L (ContinuousLinearMap.id ℂ Carrier - E) =
      (ContinuousLinearMap.id ℂ Carrier - Q) ∘L H) :
    (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C =
      H ∘L (ContinuousLinearMap.id ℂ Carrier - E) ∘L Crefl ∘L H := by
  have hleftH : (ContinuousLinearMap.id ℂ Carrier - Q) =
      H ∘L (ContinuousLinearMap.id ℂ Carrier - E) ∘L H := by
    calc
      (ContinuousLinearMap.id ℂ Carrier - Q) =
          (ContinuousLinearMap.id ℂ Carrier - Q) ∘L H ∘L H := by
            rw [hHH, ContinuousLinearMap.comp_id]
      _ = ((ContinuousLinearMap.id ℂ Carrier - Q) ∘L H) ∘L H := rfl
      _ = (H ∘L (ContinuousLinearMap.id ℂ Carrier - E)) ∘L H := by
            rw [hleft]
      _ = H ∘L (ContinuousLinearMap.id ℂ Carrier - E) ∘L H := rfl
  apply ContinuousLinearMap.ext
  intro u
  have hAtH := congrArg (fun T : Carrier →L[ℂ] Carrier => T (C u)) hleftH
  have hAtC := congrArg (fun T : Carrier →L[ℂ] Carrier => T u) hHCH
  simp only [ContinuousLinearMap.comp_apply] at hAtH hAtC ⊢
  rw [hAtH, hAtC]

set_option maxHeartbeats 20000000 in
-- the absorption chain re-associates several deep ∘L compositions, so the
-- kernel defeq pass over the assembled proof term needs the larger budget
/-- The internal-gap OUT leg of a composed boundary output
`((E_λ - P) E_λ C M J) N` is square-summable GIVEN the conjugated composite
wide-radial input fact `E_λ'' H M J = H M J` for the Hardy-Titchmarsh
conjugate `H`.  The band splits into the adjoint of the committed prolate
factor (free) and the reflected radial-boundary leg, to which B3 applies at
the reflected owner with input operator `H ∘L M`.  The support fact
`hwideHT` itself stays open. -/
theorem compositeGapLeg_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) (s : ℝ)
    (hs : 0 ≤ s)
    (M : Carrier →L[ℂ] Carrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hwideHT : radialSupportProjection (wideRadialScale lambda s) ∘L
        archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda =
        archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda) :
    Summable fun i : ρ =>
      ‖(((radialSupportProjection lambda -
            sourceSoninProjection lambda) ∘L radialSupportProjection lambda ∘L
          rootConvolution owner ∘L M ∘L sourceInclusion lambda) ∘L N)
        (sourceBasis i)‖ ^ 2 := by
  let globalBasis := compositeBasis Carrier
  let E := radialSupportProjection lambda
  let Q := sourceFourierSupportProjection lambda
  let H := archimedeanHardyTitchmarshOperator
  let B := sourceBandProjection lambda
  let C := rootConvolution owner
  let Crefl := rootConvolution (reflectedSelectedRootOwner owner)
  let J := sourceInclusion lambda
  let K := sourceProlateHilbertSchmidtFactor lambda
  have hK : Summable fun i => ‖K (globalBasis i)‖ ^ 2 :=
    sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda
  have hKadj : Summable fun i => ‖K.adjoint (globalBasis i)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq
      globalBasis globalBasis K hK
  have hfirst : Summable fun i : ρ =>
      ‖(K.adjoint ∘L C ∘L (M ∘L J ∘L N)) (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_precomp globalBasis globalBasis
      sourceBasis K.adjoint (C ∘L M ∘L J ∘L N) hKadj
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
        rw [hPComplement, sub_zero])
  have hBE : B ∘L E = B :=
    sourceBandProjection_comp_radialSupportProjection_eq_self lambda
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
  have hsplitSource : B ∘L C ∘L (M ∘L J ∘L N) =
      B ∘L Q ∘L C ∘L (M ∘L J ∘L N) + B ∘L
        (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L (M ∘L J ∘L N) := by
    apply ContinuousLinearMap.ext
    intro u
    have hu := congrArg
      (fun T : Carrier →L[ℂ] Carrier => T ((M ∘L J) (N u))) hsplit
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply] using hu
  have hsplitFactors : B ∘L C ∘L (M ∘L J ∘L N) =
      K.adjoint ∘L C ∘L (M ∘L J ∘L N) + E ∘L
        (ContinuousLinearMap.id ℂ Carrier - Q) ∘L C ∘L (M ∘L J ∘L N) := by
    apply ContinuousLinearMap.ext
    intro u
    have hu := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
      T u) hsplitSource
    have hBqAt := congrArg
      (fun T : Carrier →L[ℂ] Carrier => T (C ((M ∘L J) (N u)))) hBq
    have hBcompAt := congrArg
      (fun T : Carrier →L[ℂ] Carrier =>
        T (C ((M ∘L J) (N u))))
      hBComplement
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply] at hu hBqAt hBcompAt ⊢
    rw [hBqAt, hBcompAt] at hu
    exact hu
  have hHH : H ∘L H = ContinuousLinearMap.id ℂ Carrier := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, H]
    exact archimedeanHardyTitchmarshOperator_involutive u
  have hbaseRoot : H ∘L C ∘L H = Crefl := by
    change H ∘L cc20GlobalLogConvolution
        owner.sourceTest.involution.test ∘L H =
      cc20GlobalLogConvolution owner.sourceTest.reflection.involution.test
    exact hardyTitchmarsh_conjugate_root_eq_reflected_root owner.sourceTest
  have hHCH : H ∘L C = Crefl ∘L H := by
    apply ContinuousLinearMap.ext
    intro u
    have hAt := congrArg (fun T : Carrier →L[ℂ] Carrier =>
      T (H u)) hbaseRoot
    simp only [ContinuousLinearMap.comp_apply] at hAt
    have hAt' := hAt.symm
    simp only [H, archimedeanHardyTitchmarshOperator_involutive] at hAt'
    exact hAt'.symm
  have hleft : H ∘L
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
  have hIQC := compositeGapLeg_hIQC E Q C H Crefl hHH hHCH hleft
  have hSecondId := compositeGapLeg_secondIdentity lambda B E Q C H Crefl M J N
    hBComplement hIQC
  have hSecond := compositeRadialLeg_sourceBasis_normSq_summable
    (reflectedSelectedRootOwner owner) lambda s hs (H ∘L M) N sourceBasis
    (by
      apply ContinuousLinearMap.ext
      intro w
      have h := congrArg
        (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier => T w) hwideHT
      simpa only [ContinuousLinearMap.comp_apply] using h)
  have hSecondLeg : Summable fun i : ρ =>
      ‖((sourceBandProjection lambda ∘L archimedeanHardyTitchmarshOperator) ∘L
          ((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
            rootConvolution (reflectedSelectedRootOwner owner) ∘L
              archimedeanHardyTitchmarshOperator ∘L M ∘L
                sourceInclusion lambda) ∘L N) (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_postcomp sourceBasis
      (((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
          rootConvolution (reflectedSelectedRootOwner owner) ∘L
            archimedeanHardyTitchmarshOperator ∘L M ∘L
              sourceInclusion lambda) ∘L N)
      (sourceBandProjection lambda ∘L archimedeanHardyTitchmarshOperator)
      hSecond
  have hsum := PositiveTrace.summable_normSq_add sourceBasis
    (K.adjoint ∘L C ∘L (M ∘L J ∘L N))
    ((B ∘L H) ∘L
      ((ContinuousLinearMap.id ℂ Carrier - E) ∘L Crefl ∘L H ∘L M ∘L J ∘L
        N)) hfirst hSecondLeg
  refine hsum.congr ?_
  intro i
  congr 2
  change (ContinuousLinearMap.adjoint K ∘L C ∘L (M ∘L J ∘L N) +
      (B ∘L H) ∘L
        ((ContinuousLinearMap.id ℂ Carrier - E) ∘L Crefl ∘L H ∘L M ∘L J ∘L
          N)) (sourceBasis i) =
    ((B ∘L E) ∘L C ∘L (M ∘L J ∘L N)) (sourceBasis i)
  have hsplitPt := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
    T (sourceBasis i)) hsplitFactors
  have hSecondPt := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] Carrier =>
    T (sourceBasis i)) hSecondId
  simp only [] at hsplitPt hSecondPt
  rw [hBE, hsplitPt, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, hSecondPt]

end ConnesWeilRH.Dev
