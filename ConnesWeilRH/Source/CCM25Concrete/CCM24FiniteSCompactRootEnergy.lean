/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorUniformTrace

/-!
# Quantitative energy of the compact root boundary pair

The compact continuous root kernels already have support-polynomial
Hilbert--Schmidt energy bounds.  This module transports those bounds through
the genuine whole-line restriction maps used by the physical boundary pair.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompactRootEnergy

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open SelectedCrossingOperatorBridge
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSFixedQuotientContractionBound

/-- Restriction from whole-line `L2` to a compact kernel interval is a
contraction.  Its adjoint is the norm-preserving zero extension. -/
theorem norm_globalL2ToKernelInterval_le_one (a c b : ℝ) :
    ‖globalL2ToKernelInterval a c b‖ ≤ 1 := by
  rw [← ContinuousLinearMap.adjoint.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [norm_globalL2ToKernelInterval_adjoint_apply]
  simp only [one_mul, le_refl]

/-- The negative whole-line boundary leg has the same support-polynomial
energy bound as its compact continuous kernel. -/
theorem compactRootPairData_left_basisEnergy_le_supportPolynomial
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (∑' i, ‖(pairData g a c negativeBasis positiveBasis outputBasis
        globalBasis).left (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
  let kernelOperator := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (BoundaryNegativeInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c))
    (negativeBoundaryRootKernel g a c)
  let restriction := globalL2ToKernelInterval (a - c) 0 0
  have hKernelSummable := ContinuousKernelHilbertSchmidt.basis_normSq_summable
    (volume : Measure (BoundaryNegativeInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c))
    (negativeBoundaryRootKernel g a c) negativeBasis
  have hPrecomp := tsum_normSq_precomp_le negativeBasis outputBasis
    globalBasis kernelOperator restriction hKernelSummable
  have hRestriction : ‖restriction‖ ≤ 1 := by
    exact norm_globalL2ToKernelInterval_le_one (a - c) 0 0
  have hRestrictionSq : ‖restriction‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖restriction‖ - 1), norm_nonneg restriction]
  have hKernelNonneg :
      0 ≤ ∑' i, ‖kernelOperator (negativeBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  change (∑' i, ‖(kernelOperator ∘L restriction) (globalBasis i)‖ ^ 2) ≤ _
  calc
    _ ≤ ‖restriction‖ ^ 2 *
        (∑' i, ‖kernelOperator (negativeBasis i)‖ ^ 2) := hPrecomp
    _ ≤ 1 * (∑' i, ‖kernelOperator (negativeBasis i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hRestrictionSq hKernelNonneg
    _ ≤ (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
      simpa only [one_mul, kernelOperator] using
        negativeBoundaryRootKernel_basisEnergy_le_supportPolynomial
          g a c hac negativeBasis

/-- The positive whole-line boundary leg has the same support-polynomial
energy bound as its compact continuous kernel. -/
theorem compactRootPairData_right_basisEnergy_le_supportPolynomial
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (∑' i, ‖(pairData g a c negativeBasis positiveBasis outputBasis
        globalBasis).right (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
  let kernelOperator := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (BoundaryPositiveInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c))
    (positiveBoundaryRootKernel g a c)
  let restriction := globalL2ToKernelInterval 0 (c - a) 0
  have hKernelSummable := ContinuousKernelHilbertSchmidt.basis_normSq_summable
    (volume : Measure (BoundaryPositiveInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c))
    (positiveBoundaryRootKernel g a c) positiveBasis
  have hPrecomp := tsum_normSq_precomp_le positiveBasis outputBasis
    globalBasis kernelOperator restriction hKernelSummable
  have hRestriction : ‖restriction‖ ≤ 1 := by
    exact norm_globalL2ToKernelInterval_le_one 0 (c - a) 0
  have hRestrictionSq : ‖restriction‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖restriction‖ - 1), norm_nonneg restriction]
  have hKernelNonneg :
      0 ≤ ∑' i, ‖kernelOperator (positiveBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  change (∑' i, ‖(kernelOperator ∘L restriction) (globalBasis i)‖ ^ 2) ≤ _
  calc
    _ ≤ ‖restriction‖ ^ 2 *
        (∑' i, ‖kernelOperator (positiveBasis i)‖ ^ 2) := hPrecomp
    _ ≤ 1 * (∑' i, ‖kernelOperator (positiveBasis i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hRestrictionSq hKernelNonneg
    _ ≤ (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
      simpa only [one_mul, kernelOperator] using
        positiveBoundaryRootKernel_basisEnergy_le_supportPolynomial
          g a c hac positiveBasis

/-- Radial translation to the actual CCM24 support boundary does not increase
the negative compact-root energy. -/
theorem translatedCompactRootPairData_left_basisEnergy_le_supportPolynomial
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).left (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2 := by
  let leftTranslation := (cc20GlobalLogTranslation
    (-Real.log lambda)).toContinuousLinearMap
  let rightTranslation := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  have hleft : ‖leftTranslation‖ ≤ 1 := by
    exact (cc20GlobalLogTranslation
      (-Real.log lambda)).norm_toContinuousLinearMap_le
  have henergy := boundedSandwich_left_tsum_le_of_norm_le_one outputBasis
    (pairData owner.sourceTest a c negativeBasis positiveBasis outputBasis
      globalBasis) leftTranslation rightTranslation hleft
  calc
    _ ≤ ∑' i, ‖(pairData owner.sourceTest a c negativeBasis positiveBasis
        outputBasis globalBasis).left (globalBasis i)‖ ^ 2 := by
      simpa only [translatedCompactRootPairData, leftTranslation,
        rightTranslation] using henergy
    _ ≤ (c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2 :=
      compactRootPairData_left_basisEnergy_le_supportPolynomial
        owner.sourceTest a c hac negativeBasis positiveBasis outputBasis
        globalBasis

/-- Radial translation to the actual CCM24 support boundary does not increase
the positive compact-root energy. -/
theorem translatedCompactRootPairData_right_basisEnergy_le_supportPolynomial
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2 := by
  let leftTranslation := (cc20GlobalLogTranslation
    (-Real.log lambda)).toContinuousLinearMap
  let rightTranslation := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  have hright : ‖rightTranslation‖ ≤ 1 := by
    exact (cc20GlobalLogTranslation
      (Real.log lambda)).norm_toContinuousLinearMap_le
  have henergy := boundedSandwich_right_tsum_le_of_norm_le_one outputBasis
    (pairData owner.sourceTest a c negativeBasis positiveBasis outputBasis
      globalBasis) leftTranslation rightTranslation hright
  calc
    _ ≤ ∑' i, ‖(pairData owner.sourceTest a c negativeBasis positiveBasis
        outputBasis globalBasis).right (globalBasis i)‖ ^ 2 := by
      simpa only [translatedCompactRootPairData, leftTranslation,
        rightTranslation] using henergy
    _ ≤ (c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2 :=
      compactRootPairData_right_basisEnergy_le_supportPolynomial
        owner.sourceTest a c hac negativeBasis positiveBasis outputBasis
        globalBasis

end CCM24FiniteSCompactRootEnergy
end CCM25Concrete
end Source
end ConnesWeilRH
