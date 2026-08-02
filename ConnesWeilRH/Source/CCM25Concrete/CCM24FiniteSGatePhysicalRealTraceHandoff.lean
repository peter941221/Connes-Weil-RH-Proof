/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalNormalizedRealTraceReduction

/-!
# Route-facing real-trace handoff for the finite-S Gate

Proof 751 identifies the real trace of the normalized symmetric response with
the real part of one complete physical full-kernel scalar.  The original Gate
owner is the nonlinear remainder, which differs from that target by the
already controlled first jet.

This module keeps that first jet explicitly and proves the exact route-facing
equivalence

`uniform |Re Tr(remainder_S)| <-> uniform |Re FullKernelTrace_S|`.

The result does not bound either side.  It also does not imply the stronger
uniform complex-norm Gate used by older interfaces.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalRealTraceHandoff

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalLeakageTraceReduction
open CCM24FiniteSGatePhysicalNormalizedGradedCoboundary
open CCM24FiniteSGatePhysicalNormalizedRealTraceReduction
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24FiniteSGatePhysicalSignedDiagonal
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSSourceFirstJetSupportBound
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The family-independent trace majorant already proved for the first jet. -/
noncomputable def sourceFirstJetTraceMajorant
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier) : ℝ :=
  (12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
      (globalBasis i)‖ ^ 2)) *
    ((c - a) ^ 2 *
      SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2)

section FixedFamily

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale)
variable (family : FinitePrimePowerFamily)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {iota kappa tau iotaR kappaR tauR nu mu sigma rho : Type*}
variable (negativeBasis : HilbertBasis iota ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis kappa ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis tau ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis iotaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis kappaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis tauR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
variable (pairedBoundaryBasis : HilbertBasis sigma ℂ
  (actualBandPairCarrier a c))
variable (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

include a c hac hsupp negativeBasis positiveBasis outputBasis
  reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
  globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor

/-- The real part of the first-jet trace inherits its known norm majorant. -/
theorem abs_re_ordinaryTraceAlong_sourceFirstJet_le_majorant :
    |(ordinaryTraceAlong sourceBasis
      (sourceActualBandFiniteEulerSoninResponse
        owner lambda family)).re| ≤
      sourceFirstJetTraceMajorant owner lambda a c globalBasis := by
  exact (Complex.abs_re_le_norm _).trans (by
    simpa only [sourceFirstJetTraceMajorant] using
      (sourceActualBandFiniteEulerSoninTrace_norm_le_supportEnergy owner
        lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor))

/-- Exact real-scalar ledger: the nonlinear Gate remainder is the controlled
first jet plus the real part of the complete physical full-kernel scalar. -/
theorem ordinaryTraceAlong_lowerFactorGaugedResponse_re_eq_firstJet_add_fullKernel_re :
    (ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)).re =
      (ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerSoninResponse owner lambda family)).re +
      (finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis).re := by
  have hfirst :=
    sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hleakage :=
    sourceGatePhysicalLeakageCrossingResponse_isTraceClassAlong owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hsplit :=
    ordinaryTraceAlong_lowerFactorGaugedResponse_eq_firstJet_add_leakage
      owner lambda family sourceBasis hfirst hleakage
  have hleakageKernel :
      (ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalLeakageCrossingResponse
          owner lambda family)).re =
        (finiteEulerObliqueShearFullKernelTrace owner lambda family a c
          sourceBasis).re := by
    calc
      _ = (star (ordinaryTraceAlong sourceBasis
          (sourceGatePhysicalLeakageCrossingResponse
            owner lambda family))).re := by
        rw [Complex.star_def, Complex.conj_re]
      _ = (ordinaryTraceAlong sourceBasis
          (finiteEulerTargetCommutatorResponse owner lambda family)).re := by
        rw [ordinaryTraceAlong_targetCommutator_eq_star_leakage]
      _ = _ := congrArg Complex.re
        (ordinaryTraceAlong_targetCommutator_eq_obliqueShearFullKernelTrace
          owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis sourceBasis hfactor)
  rw [hsplit, Complex.add_re, hleakageKernel]

/-- A full-kernel real bound gives a Gate-remainder real bound with only the
already known first-jet cost. -/
theorem abs_re_lowerFactorGaugedResponse_le_firstJetMajorant_add_fullKernelBound
    (kernelBound : ℝ)
    (hkernel :
      |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis).re| ≤ kernelBound) :
    |(ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)).re| ≤
      sourceFirstJetTraceMajorant owner lambda a c globalBasis +
        kernelBound := by
  rw [ordinaryTraceAlong_lowerFactorGaugedResponse_re_eq_firstJet_add_fullKernel_re
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_re_ordinaryTraceAlong_sourceFirstJet_le_majorant owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)
    hkernel)

/-- Conversely, the complete full-kernel real scalar costs at most the Gate
remainder real trace plus the known first jet. -/
theorem abs_fullKernel_re_le_abs_re_lowerFactor_add_firstJetMajorant :
    |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
      sourceBasis).re| ≤
      |(ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)).re| +
        sourceFirstJetTraceMajorant owner lambda a c globalBasis := by
  have hledger :=
    ordinaryTraceAlong_lowerFactorGaugedResponse_re_eq_firstJet_add_fullKernel_re
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hsolve :
      (finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis).re =
        (ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family)).re -
          (ordinaryTraceAlong sourceBasis
            (sourceActualBandFiniteEulerSoninResponse
              owner lambda family)).re := by
    linarith
  have hfirstReal :=
    abs_re_ordinaryTraceAlong_sourceFirstJet_le_majorant owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  rw [hsolve, sub_eq_add_neg]
  calc
    |(ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family)).re +
        -(ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerSoninResponse
            owner lambda family)).re| ≤
      |(ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family)).re| +
        |-(ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerSoninResponse
            owner lambda family)).re| := abs_add_le _ _
    _ = |(ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family)).re| +
        |(ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerSoninResponse
            owner lambda family)).re| := by rw [abs_neg]
    _ ≤ _ := add_le_add (le_refl _) hfirstReal

end FixedFamily

section UniformFamily

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {iota kappa tau iotaR kappaR tauR nu mu sigma rho : Type*}
variable (negativeBasis : HilbertBasis iota ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis kappa ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis tau ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis iotaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis kappaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis tauR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
variable (pairedBoundaryBasis : HilbertBasis sigma ℂ
  (actualBandPairCarrier a c))
variable (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

include a c hac hsupp negativeBasis positiveBasis outputBasis
  reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
  globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor

/-- The honest real Gate contract is exactly the real bound on the complete
physical full-kernel scalar.  The old complex-norm Gate remains stronger. -/
theorem exists_uniform_lowerFactorGaugedRealTraceBound_iff_fullKernelRealBound :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      |(ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)).re| ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis).re| ≤ bound) := by
  constructor
  · rintro ⟨gateBound, hgate⟩
    refine ⟨gateBound +
      sourceFirstJetTraceMajorant owner lambda a c globalBasis, fun family =>
        ?_⟩
    exact
      (abs_fullKernel_re_le_abs_re_lowerFactor_add_firstJetMajorant owner
        lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor).trans
      (add_le_add (hgate family) (le_refl _))
  · rintro ⟨kernelBound, hkernel⟩
    refine ⟨sourceFirstJetTraceMajorant owner lambda a c globalBasis +
      kernelBound, fun family => ?_⟩
    exact
      abs_re_lowerFactorGaugedResponse_le_firstJetMajorant_add_fullKernelBound
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis pairedBoundaryBasis
        sourceBasis hfactor kernelBound (hkernel family)

/-- Equivalently, the real Gate remainder is uniformly bounded exactly when
the normalized symmetric trace from Proof 751 is uniformly bounded. -/
theorem exists_uniform_lowerFactorGaugedRealTraceBound_iff_symmetricTraceBound :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      |(ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)).re| ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedSymmetricBoundaryResponse
          owner lambda family)‖ ≤ bound) := by
  calc
    _ ↔ ∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
        |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
          sourceBasis).re| ≤ bound :=
      exists_uniform_lowerFactorGaugedRealTraceBound_iff_fullKernelRealBound
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    _ ↔ _ :=
      (exists_uniform_normalizedSymmetricTraceBound_iff_fullKernelRealBound
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor).symm

end UniformFamily

end CCM24FiniteSGatePhysicalRealTraceHandoff
end CCM25Concrete
end Source
end ConnesWeilRH
