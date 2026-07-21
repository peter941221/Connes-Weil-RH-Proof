/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorRootPairing
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMultiRenewal

/-!
# Renewal root pairing for the completed finite-Euler response

The complete finite-Euler corner is factored before the causal probability
average is expanded.  Its right leg is the single bounded operator
`C R A_S B`.  For each fixed input vector, the normalized inverse `A_S` is
then expanded into its absolutely summable renewal series.

On a named Hilbert basis this gives the ordered scalar series
`sum_i sum_omega`.  The module does not exchange those two sums and does not
identify the result with a sum of atomwise traces.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorRenewalRootPairing

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSMultiRenewal
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSRootCompletedDetectorCommutator
open CCM24FiniteSRootCompletedDetectorRootPairing

/-- The selected compact root after the complete finite-Euler Sonin crossing.
This is one bounded right leg; no renewal atom has yet been exposed. -/
noncomputable def sourceDetectorFiniteEulerSoninRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L sourceSoninProjection lambda ∘L
    normalizedFiniteEulerInverse family ∘L sourceBandProjection lambda

/-- The complete finite-Euler corner is the ordered product of the fixed left
root leg and the unexpanded finite-Euler right root leg. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_rootTraceProduct
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      (sourceDetectorBandRootLeg owner lambda).adjoint ∘L
        sourceDetectorFiniteEulerSoninRootLeg owner lambda family := by
  rw [sourceRootCompletedFixedQuotientCorner_eq_unsplitRootPair,
    sourceRootCompletedFiniteEulerCommonRightLeg_eq_causalCrossing]
  rfl

/-- Every matrix coefficient of the complete finite-Euler corner is one
cross pairing of the fixed and averaged compact-root legs. -/
theorem sourceRootCompletedFiniteEulerCorner_inner_eq_rootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : finiteSCarrier) :
    inner ℂ x
        (sourceRootCompletedFixedQuotientCorner owner lambda
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L
            radialSupportProjection lambda) y) =
      inner ℂ (sourceDetectorBandRootLeg owner lambda x)
        (sourceDetectorFiniteEulerSoninRootLeg owner lambda family y) := by
  rw [sourceRootCompletedFiniteEulerCorner_eq_rootTraceProduct,
    ContinuousLinearMap.comp_apply]
  exact (sourceDetectorBandRootLeg owner lambda).adjoint_inner_right x
    (sourceDetectorFiniteEulerSoninRootLeg owner lambda family y)

/-- Vector-level renewal expansion of the complete right root leg.  The
series is formed only after the input vector is fixed. -/
theorem sourceDetectorFiniteEulerSoninRootLeg_apply_eq_renewal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (u : finiteSCarrier) :
    sourceDetectorFiniteEulerSoninRootLeg owner lambda family u =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        (finiteEulerRenewalWeight family.visiblePrimes index : ℂ) •
          sourceDetectorTranslatedSoninRootLeg owner lambda
            (finiteEulerRenewalDisplacement family.visiblePrimes index) u := by
  let postprocess :=
    rootConvolution owner ∘L sourceSoninProjection lambda
  have hsummable := summable_finiteEulerRenewalTerm family.visiblePrimes
    (sourceBandProjection lambda u)
  rw [sourceDetectorFiniteEulerSoninRootLeg]
  simp only [ContinuousLinearMap.comp_apply]
  rw [normalizedFiniteEulerInverse_apply_eq_multiRenewal]
  change postprocess
      (∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerRenewalTerm family.visiblePrimes
          (sourceBandProjection lambda u) index) = _
  rw [postprocess.map_tsum hsummable]
  apply tsum_congr
  intro index
  simp only [finiteEulerRenewalTerm, postprocess,
    sourceDetectorTranslatedSoninRootLeg,
    ContinuousLinearMap.comp_apply, map_smul,
    LinearIsometry.coe_toContinuousLinearMap]

/-- For fixed vectors, the weighted renewal root pairings are summable.  This
is the inner summability needed for the ordered `sum_i sum_omega` formula. -/
theorem summable_sourceDetectorFiniteEulerRootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : finiteSCarrier) :
    Summable fun index : FiniteEulerRenewalIndex family.visiblePrimes =>
      (finiteEulerRenewalWeight family.visiblePrimes index : ℂ) *
        inner ℂ (sourceDetectorBandRootLeg owner lambda x)
          (sourceDetectorTranslatedSoninRootLeg owner lambda
            (finiteEulerRenewalDisplacement family.visiblePrimes index) y) := by
  let coefficient : finiteSCarrier →L[ℂ] ℂ :=
    (innerSL ℂ (sourceDetectorBandRootLeg owner lambda x)).comp
      (rootConvolution owner ∘L sourceSoninProjection lambda)
  have hsummable := summable_finiteEulerRenewalTerm family.visiblePrimes
    (sourceBandProjection lambda y)
  have hmapped := coefficient.summable hsummable
  simpa only [coefficient, finiteEulerRenewalTerm,
    sourceDetectorTranslatedSoninRootLeg,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul,
    inner_smul_right] using hmapped

/-- The averaged root pairing is the renewal sum for fixed vectors.  The
continuous inner-product functional is applied before taking the `tsum`. -/
theorem sourceDetectorFiniteEulerRootPairing_eq_renewal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : finiteSCarrier) :
    inner ℂ (sourceDetectorBandRootLeg owner lambda x)
        (sourceDetectorFiniteEulerSoninRootLeg owner lambda family y) =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        (finiteEulerRenewalWeight family.visiblePrimes index : ℂ) *
          inner ℂ (sourceDetectorBandRootLeg owner lambda x)
            (sourceDetectorTranslatedSoninRootLeg owner lambda
              (finiteEulerRenewalDisplacement family.visiblePrimes index)
              y) := by
  let coefficient : finiteSCarrier →L[ℂ] ℂ :=
    (innerSL ℂ (sourceDetectorBandRootLeg owner lambda x)).comp
      (rootConvolution owner ∘L sourceSoninProjection lambda)
  have hsummable := summable_finiteEulerRenewalTerm family.visiblePrimes
    (sourceBandProjection lambda y)
  rw [sourceDetectorFiniteEulerSoninRootLeg]
  simp only [ContinuousLinearMap.comp_apply]
  rw [normalizedFiniteEulerInverse_apply_eq_multiRenewal]
  change coefficient
      (∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerRenewalTerm family.visiblePrimes
          (sourceBandProjection lambda y) index) = _
  rw [coefficient.map_tsum hsummable]
  apply tsum_congr
  intro index
  simp only [coefficient, finiteEulerRenewalTerm,
    sourceDetectorTranslatedSoninRootLeg,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul,
    smul_eq_mul, LinearIsometry.coe_toContinuousLinearMap]

/-- The root pairing attached to one basis vector after the complete
finite-Euler probability average has been formed. -/
noncomputable def rootCompletedDetectorFiniteEulerRootPairingDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (index : ν) : ℂ :=
  inner ℂ
    (sourceDetectorBandRootLeg owner lambda (globalBasis index))
    (sourceDetectorFiniteEulerSoninRootLeg owner lambda family
      (globalBasis index))

/-- Each fixed basis diagonal has an absolutely summable inner renewal
series. -/
theorem summable_rootCompletedDetectorTranslationRootPairingDiagonal_weighted
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (index : ν) :
    Summable fun renewalIndex :
        FiniteEulerRenewalIndex family.visiblePrimes =>
      (finiteEulerRenewalWeight family.visiblePrimes renewalIndex : ℂ) *
        rootCompletedDetectorTranslationRootPairingDiagonal owner lambda
          (finiteEulerRenewalDisplacement family.visiblePrimes renewalIndex)
          globalBasis index := by
  simpa only [rootCompletedDetectorTranslationRootPairingDiagonal] using
    summable_sourceDetectorFiniteEulerRootPairing owner lambda family
      (globalBasis index) (globalBasis index)

/-- The finite-Euler diagonal is the inner renewal `tsum`; the global basis
index remains fixed throughout this equality. -/
theorem rootCompletedDetectorFiniteEulerRootPairingDiagonal_eq_renewal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (index : ν) :
    rootCompletedDetectorFiniteEulerRootPairingDiagonal owner lambda family
        globalBasis index =
      ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
        (finiteEulerRenewalWeight family.visiblePrimes renewalIndex : ℂ) *
          rootCompletedDetectorTranslationRootPairingDiagonal owner lambda
            (finiteEulerRenewalDisplacement family.visiblePrimes renewalIndex)
            globalBasis index := by
  unfold rootCompletedDetectorFiniteEulerRootPairingDiagonal
  exact sourceDetectorFiniteEulerRootPairing_eq_renewal owner lambda family
    (globalBasis index) (globalBasis index)

/-- The complete physical three-branch pair, sandwiched only after the full
finite-Euler right leg has been formed, owns the one-sided corner. -/
noncomputable def sourceRootCompletedFiniteEulerPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) globalBasis :=
  ((sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor).boundedSandwich
    boundaryBasis (sourceBandProjection lambda)
      (sourceSoninProjection lambda ∘L
        normalizedFiniteEulerInverse family ∘L
        sourceBandProjection lambda)).smulRight (-1)

/-- The physical pair's trace product is exactly the unexpanded complete
finite-Euler corner. -/
theorem sourceRootCompletedFiniteEulerPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceRootCompletedFiniteEulerPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor).traceProduct =
      sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) := by
  have hcommutator :
      CCM24FiniteSTwoSidedRootRecombination.commutator
          (detectorOperator owner) (sourceSoninProjection lambda) =
        -cc20Commutator (sourceSoninProjection lambda)
          (detectorOperator owner) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [CCM24FiniteSTwoSidedRootRecombination.commutator,
      cc20Commutator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply]
    abel
  rw [sourceRootCompletedFiniteEulerPairData,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor,
    ← sourceSoninCommutator_eq_threeBranch]
  rw [sourceRootCompletedFiniteEulerCorner_eq_fixedCommutatorSandwich,
    hcommutator]
  apply ContinuousLinearMap.ext
  intro u
  simp only [neg_one_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_neg]

/-- Trace legality belongs to the complete finite-Euler corner itself.  It is
not obtained by summing trace norms of the renewal atoms. -/
theorem sourceRootCompletedFiniteEulerCorner_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong globalBasis
      (sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda)) := by
  rw [← sourceRootCompletedFiniteEulerPairData_traceProduct_eq owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor]
  exact (sourceRootCompletedFiniteEulerPairData owner lambda family a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    hfactor).traceProduct_isTraceClassAlong

/-- The outer diagonal series of averaged root pairings is summable because
the complete physical pair owns the operator before renewal expansion. -/
theorem summable_rootCompletedDetectorFiniteEulerRootPairingDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    Summable (rootCompletedDetectorFiniteEulerRootPairingDiagonal owner lambda
      family globalBasis) := by
  have htrace := sourceRootCompletedFiniteEulerCorner_isTraceClassAlong owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor
  rw [IsTraceClassAlong] at htrace
  exact htrace.congr fun index =>
    sourceRootCompletedFiniteEulerCorner_inner_eq_rootPairing owner lambda
      family (globalBasis index) (globalBasis index)

/-- The legal finite-Euler trace has the ordered form `sum_i sum_omega`.
Neither this theorem nor its proof exchanges the basis and renewal sums. -/
theorem sourceRootCompletedFiniteEulerTrace_eq_iterated_rootPairing_tsum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    ordinaryTraceAlong globalBasis
        (sourceRootCompletedFixedQuotientCorner owner lambda
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L
            radialSupportProjection lambda)) =
      ∑' index : ν,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          (finiteEulerRenewalWeight family.visiblePrimes renewalIndex : ℂ) *
            rootCompletedDetectorTranslationRootPairingDiagonal owner lambda
              (finiteEulerRenewalDisplacement family.visiblePrimes renewalIndex)
              globalBasis index := by
  rw [ordinaryTraceAlong]
  apply tsum_congr
  intro index
  rw [sourceRootCompletedFiniteEulerCorner_inner_eq_rootPairing]
  exact rootCompletedDetectorFiniteEulerRootPairingDiagonal_eq_renewal owner
    lambda family globalBasis index

end CCM24FiniteSRootCompletedDetectorRenewalRootPairing
end CCM25Concrete
end Source
end ConnesWeilRH
