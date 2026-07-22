/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompactRootEnergy

/-!
# Quantitative energy of the reflected second-support root pair

The reflected compact root is transported first by radial translations and
then by the archimedean Hardy--Titchmarsh unitary.  Both transports are
contractions, so the primitive support-polynomial energy survives on the
actual source second-support carrier.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSReflectedRootEnergy

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open CCM24ReflectedCompactRoot
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSCompactRootEnergy

/-- The concrete Hardy--Titchmarsh operator is a contraction because its
underlying linear isometry equivalence preserves every vector norm. -/
theorem norm_archimedeanHardyTitchmarshOperator_le_one :
    ‖archimedeanHardyTitchmarshOperator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖ccm24ArchimedeanHardyTitchmarsh u‖ ≤ 1 * ‖u‖
  rw [ccm24ArchimedeanHardyTitchmarsh.norm_map]
  exact (one_mul ‖u‖).ge

/-- Reflection preserves the order-zero Schwartz seminorm exactly. -/
theorem seminorm_zero_zero_reflection_eq
    (g : CompactLogConvolution.CompactLogTest) :
    SchwartzMap.seminorm ℂ 0 0 g.reflection.test =
      SchwartzMap.seminorm ℂ 0 0 g.test := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℂ 0 0 _ (by positivity)
    intro x
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
      CompactLogConvolution.CompactLogTest.reflection_apply] using
      (SchwartzMap.norm_le_seminorm ℂ g.test (-x))
  · apply SchwartzMap.seminorm_le_bound ℂ 0 0 _ (by positivity)
    intro x
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
      CompactLogConvolution.CompactLogTest.reflection_apply, neg_neg] using
      (SchwartzMap.norm_le_seminorm ℂ g.reflection.test (-x))

/-- The radially translated reflected pair keeps the negative-leg compact
support energy. -/
theorem reflectedTranslatedCompactRootPairData_left_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(reflectedTranslatedCompactRootPairData owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis).left
        (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 := by
  let leftTranslation := (cc20GlobalLogTranslation
    (-Real.log lambda)).toContinuousLinearMap
  let rightTranslation := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  have hleft : ‖leftTranslation‖ ≤ 1 := by
    exact (cc20GlobalLogTranslation
      (-Real.log lambda)).norm_toContinuousLinearMap_le
  have henergy := boundedSandwich_left_tsum_le_of_norm_le_one outputBasis
    (pairData owner.sourceTest.reflection (-c) (-a) negativeBasis
      positiveBasis outputBasis globalBasis) leftTranslation rightTranslation
      hleft
  calc
    _ ≤ ∑' i, ‖(pairData owner.sourceTest.reflection (-c) (-a)
        negativeBasis positiveBasis outputBasis globalBasis).left
        (globalBasis i)‖ ^ 2 := by
      simpa only [reflectedTranslatedCompactRootPairData, leftTranslation,
        rightTranslation] using henergy
    _ ≤ ((-a) - (-c)) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 :=
      compactRootPairData_left_basisEnergy_le_supportPolynomial
        owner.sourceTest.reflection (-c) (-a) (by linarith) negativeBasis
        positiveBasis outputBasis globalBasis
    _ = (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 := by ring

/-- The radially translated reflected pair keeps the positive-leg compact
support energy. -/
theorem reflectedTranslatedCompactRootPairData_right_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(reflectedTranslatedCompactRootPairData owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis).right
        (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 := by
  let leftTranslation := (cc20GlobalLogTranslation
    (-Real.log lambda)).toContinuousLinearMap
  let rightTranslation := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  have hright : ‖rightTranslation‖ ≤ 1 := by
    exact (cc20GlobalLogTranslation
      (Real.log lambda)).norm_toContinuousLinearMap_le
  have henergy := boundedSandwich_right_tsum_le_of_norm_le_one outputBasis
    (pairData owner.sourceTest.reflection (-c) (-a) negativeBasis
      positiveBasis outputBasis globalBasis) leftTranslation rightTranslation
      hright
  calc
    _ ≤ ∑' i, ‖(pairData owner.sourceTest.reflection (-c) (-a)
        negativeBasis positiveBasis outputBasis globalBasis).right
        (globalBasis i)‖ ^ 2 := by
      simpa only [reflectedTranslatedCompactRootPairData, leftTranslation,
        rightTranslation] using henergy
    _ ≤ ((-a) - (-c)) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 :=
      compactRootPairData_right_basisEnergy_le_supportPolynomial
        owner.sourceTest.reflection (-c) (-a) (by linarith) negativeBasis
        positiveBasis outputBasis globalBasis
    _ = (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 := by ring

/-- The Hardy--Titchmarsh transport does not increase the reflected negative
leg on the actual source second-support carrier. -/
theorem sourceSecondSupportCompactRootPairData_left_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(sourceSecondSupportCompactRootPairData owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis).left
        (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 := by
  have hHardy : ‖archimedeanHardyTitchmarshOperator‖ ≤ 1 := by
    exact norm_archimedeanHardyTitchmarshOperator_le_one
  have henergy := boundedSandwich_left_tsum_le_of_norm_le_one outputBasis
    (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis)
    archimedeanHardyTitchmarshOperator
    archimedeanHardyTitchmarshOperator hHardy
  calc
    _ ≤ ∑' i, ‖(reflectedTranslatedCompactRootPairData owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis).left
        (globalBasis i)‖ ^ 2 := by
      simpa only [sourceSecondSupportCompactRootPairData] using henergy
    _ ≤ (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 :=
      reflectedTranslatedCompactRootPairData_left_basisEnergy_le owner lambda
        a c hac negativeBasis positiveBasis outputBasis globalBasis

/-- The Hardy--Titchmarsh transport does not increase the reflected positive
leg on the actual source second-support carrier. -/
theorem sourceSecondSupportCompactRootPairData_right_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(sourceSecondSupportCompactRootPairData owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis).right
        (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 := by
  have hHardy : ‖archimedeanHardyTitchmarshOperator‖ ≤ 1 := by
    exact norm_archimedeanHardyTitchmarshOperator_le_one
  have henergy := boundedSandwich_right_tsum_le_of_norm_le_one outputBasis
    (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis)
    archimedeanHardyTitchmarshOperator
    archimedeanHardyTitchmarshOperator hHardy
  calc
    _ ≤ ∑' i, ‖(reflectedTranslatedCompactRootPairData owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis).right
        (globalBasis i)‖ ^ 2 := by
      simpa only [sourceSecondSupportCompactRootPairData] using henergy
    _ ≤ (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0
        owner.sourceTest.reflection.test ^ 2 :=
      reflectedTranslatedCompactRootPairData_right_basisEnergy_le owner lambda
        a c hac negativeBasis positiveBasis outputBasis globalBasis

/-- The actual second-support negative leg is controlled by the original,
unreflected root seminorm. -/
theorem sourceSecondSupportCompactRootPairData_left_basisEnergy_le_original
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(sourceSecondSupportCompactRootPairData owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis).left
        (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2 := by
  simpa only [seminorm_zero_zero_reflection_eq] using
    sourceSecondSupportCompactRootPairData_left_basisEnergy_le owner lambda
      a c hac negativeBasis positiveBasis outputBasis globalBasis

/-- The actual second-support positive leg is controlled by the original,
unreflected root seminorm. -/
theorem sourceSecondSupportCompactRootPairData_right_basisEnergy_le_original
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(sourceSecondSupportCompactRootPairData owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis).right
        (globalBasis i)‖ ^ 2) ≤
      (c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2 := by
  simpa only [seminorm_zero_zero_reflection_eq] using
    sourceSecondSupportCompactRootPairData_right_basisEnergy_le owner lambda
      a c hac negativeBasis positiveBasis outputBasis globalBasis

end CCM24FiniteSReflectedRootEnergy
end CCM25Concrete
end Source
end ConnesWeilRH
