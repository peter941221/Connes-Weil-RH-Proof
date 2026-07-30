/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawLocalTraceFactorization

/-!
# The actual local-pair owner of the signed interior

The local raw-defect pair has the orientation

```text
traceProduct = left^dagger * right = localRawDefect.
```

Swapping its two Hilbert--Schmidt legs therefore owns the adjoint in the
opposite order, `right^dagger * left = localRawDefect^dagger`.  The exact
two-sided cofactor from Proof 623 then gives a pair owner for the genuine
signed compressed interior:

```text
-rho_p^-1 * Transition^dagger * localRawDefect^dagger * Reverse^dagger
  = signedCompressedInteriorOwner.
```

This is fixed-suffix operator ownership only.  It introduces no
family-uniform estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalPairOwner

open scoped InnerProduct InnerProductSpace

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24SourceProlateTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The full two-coordinate target carrier of the actual local raw-defect
pair.  This is one `WithLp 2` layer larger than the paired boundary carrier
used while constructing either coordinate. -/
abbrev localRawDefectPairTarget (a c : ℝ) :=
  WithLp 2
    (WithLp 2
        (commonBoundaryCarrier a c × commonBoundaryCarrier a c) ×
      WithLp 2
        (commonBoundaryCarrier a c × commonBoundaryCarrier a c))

/-! ## The actual swapped local-defect pair -/

/-- Swapping the actual local raw-defect pair owns the adjoint local defect.
The equality retains the noncommutative order `right^dagger * left`. -/
theorem suffixActualBandLocalRawDefectPairData_swap_traceProduct_eq_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (suffixActualBandLocalRawDefectPairData owner lambda p S a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis pairedBoundaryBasis hfactor).swap.traceProduct =
        (suffixActualBandLocalRawDefect owner lambda p S)† := by
  rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint,
    suffixActualBandLocalRawDefectPairData_traceProduct_eq]

/-! ## Pair ownership of the signed interior -/

/-- The actual local pair, swapped, dressed by the two adjoint Schur maps,
and scaled by the exact nonzero Markov cofactor.  The separate target basis is
for the full nested pair carrier, not the one-pair boundary carrier. -/
noncomputable def suffixActualBandSignedCompressedInteriorPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma chi : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (localDefectTargetBasis : HilbertBasis chi ℂ
      (localRawDefectPairTarget a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := localRawDefectPairTarget a c) sourceBasis :=
  ((((suffixActualBandLocalRawDefectPairData owner lambda p S a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis pairedBoundaryBasis hfactor).swap).boundedSandwich
        localDefectTargetBasis
        ((suffixEulerFrameTransition lambda p S)†)
        ((suffixEulerFrameReverseTransition lambda p S)†)).smulRight
      (-((primeSchurMarkovScalar p : ℂ)⁻¹)))

/-- The constructed pair product is the exact scaled two-sided adjoint
cofactor.  This theorem makes the factor order independently auditable. -/
theorem suffixActualBandSignedCompressedInteriorPairData_traceProduct_eq_cofactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma chi : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (localDefectTargetBasis : HilbertBasis chi ℂ
      (localRawDefectPairTarget a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (suffixActualBandSignedCompressedInteriorPairData owner lambda p S a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis pairedBoundaryBasis localDefectTargetBasis hfactor).traceProduct =
        (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
          ((suffixEulerFrameTransition lambda p S)† ∘L
            (suffixActualBandLocalRawDefect owner lambda p S)† ∘L
              (suffixEulerFrameReverseTransition lambda p S)†) := by
  have hswap :=
    suffixActualBandLocalRawDefectPairData_swap_traceProduct_eq_adjoint
      owner lambda p S a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor
  rw [suffixActualBandSignedCompressedInteriorPairData,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
  exact congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
        ((suffixEulerFrameTransition lambda p S)† ∘L operator ∘L
          (suffixEulerFrameReverseTransition lambda p S)†)) hswap

/-- The actual pair product is the genuine signed compressed interior owner.
No norm or trace estimate is used in this identification. -/
theorem suffixActualBandSignedCompressedInteriorPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma chi : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (localDefectTargetBasis : HilbertBasis chi ℂ
      (localRawDefectPairTarget a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (suffixActualBandSignedCompressedInteriorPairData owner lambda p S a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis pairedBoundaryBasis localDefectTargetBasis hfactor).traceProduct =
        signedCompressedInteriorOwner owner lambda p S := by
  rw [suffixActualBandSignedCompressedInteriorPairData_traceProduct_eq_cofactor]
  have hscalar : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hcofactor :=
    transitionAdjoint_comp_localRawDefectAdjoint_comp_reverseAdjoint_eq_neg_scalar_interior
      owner lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hcofactorPoint := DFunLike.congr_fun hcofactor x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply] at hcofactorPoint ⊢
  rw [hcofactorPoint]
  simp only [smul_neg, smul_smul]
  simp [hscalar]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalPairOwner
end CCM25Concrete
end Source
end ConnesWeilRH
