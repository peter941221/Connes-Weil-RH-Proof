/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawLocalTraceFactorization

/-!
# Swapped local-pair bridge to the finite radial column

The complete local Hilbert--Schmidt pair may be swapped without splitting its
outer, reflected, second-support, or prolate branches.  After the adjoint
reverse transition is appended, its trace product is exactly

```text
  localRawDefect^dagger * Reverse^dagger
    = -rho_p * completeBoundaryReverseIntertwiningDefect.
```

This is the same cofactor that produces the antiresonant interior after the
adjoint forward transition is applied.  It is not, by itself, a factorization
through Proof 639's finite radial-block column.

The second half of the module states the exact extra Douglas premise needed
for such a finite-column factorization.  If that premise is supplied, the
finite column and its norm-`32` readout give a raw Bone 1 readout with norm at
most `256 * bound`.  No finite-column factor, uniform bound, Gate 3U estimate,
sign statement, or RH conclusion is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSDouglasFactor
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The complete swapped cofactor -/

/-- The complete cofactor obtained by swapping the local physical pair and
then appending the adjoint reverse transition.  This definition is independent
of the Hilbert bases used to own the local trace-class product. -/
noncomputable def suffixActualBandCompleteSwappedLocalCofactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixActualBandLocalRawDefect owner lambda p S)† ∘L
    (suffixEulerFrameReverseTransition lambda p S)†

/-- Swapping an arbitrary valid local pair owner produces the basis-free
complete cofactor.  No Hilbert--Schmidt leg is estimated separately. -/
theorem swappedLocalPair_traceProduct_comp_reverseAdjoint_eq_completeCofactor
    {iota G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace Complex G] [CompleteSpace G]
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis iota Complex (sourceSoninCarrier lambda))
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (hdata : data.traceProduct =
      suffixActualBandLocalRawDefect owner lambda p S) :
    data.swap.traceProduct ∘L
        (suffixEulerFrameReverseTransition lambda p S)† =
      suffixActualBandCompleteSwappedLocalCofactor owner lambda p S := by
  rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hdata]
  rfl

/-- The swapped cofactor is exactly the complete reverse-intertwining defect,
with the genuine Schur--Markov scalar and sign. -/
theorem suffixActualBandCompleteSwappedLocalCofactor_eq_neg_scalar_smul_completeBoundaryDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompleteSwappedLocalCofactor owner lambda p S =
      -((primeSchurMarkovScalar p : Complex) •
        suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S) := by
  have hcofactor :=
    completeBoundaryReverseIntertwiningDefect_comp_transitionAdjoint_eq_neg_localRawDefectAdjoint
      owner lambda p S
  have hpair :=
    suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
      lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hcofactorPoint := DFunLike.congr_fun hcofactor
    (((suffixEulerFrameReverseTransition lambda p S)†) x)
  have hpairPoint := DFunLike.congr_fun hpair x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.neg_apply] at hcofactorPoint hpairPoint ⊢
  rw [hpairPoint, map_smul] at hcofactorPoint
  simpa only [neg_neg] using (congrArg Neg.neg hcofactorPoint).symm

/-- Expanded same-object ledger.  Each adjacent response still contains the
whole three-branch commutator, so the reflected second-support and prolate
pieces cannot be assigned independent norms at this boundary. -/
theorem suffixActualBandCompleteSwappedLocalCofactor_eq_coupledBoundaryLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompleteSwappedLocalCofactor owner lambda p S =
      -((primeSchurMarkovScalar p : Complex) •
        ((suffixEulerFrameReverseTransition lambda p S)† ∘L
            suffixActualBandCompleteBoundaryResponse owner lambda S -
          suffixActualBandCompleteBoundaryResponse owner lambda (p :: S) ∘L
            (suffixEulerFrameReverseTransition lambda p S)†)) := by
  rw [suffixActualBandCompleteSwappedLocalCofactor_eq_neg_scalar_smul_completeBoundaryDefect]
  rfl

/-- The literal local pair from the physical four-branch owner satisfies the
same coupled ledger.  This is the requested bridge from the complete swapped
pair expression; no basis-energy estimate enters the proof. -/
theorem suffixActualBandLocalRawDefectPairData_swap_traceProduct_comp_reverseAdjoint_eq_coupledBoundaryLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : Real) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
    (negativeBasis : HilbertBasis iota Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu Complex finiteSCarrier)
    (boundaryBasis : HilbertBasis mu Complex (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma Complex
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (suffixActualBandLocalRawDefectPairData owner lambda p S a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis pairedBoundaryBasis hfactor).swap.traceProduct ∘L
          (suffixEulerFrameReverseTransition lambda p S)† =
      -((primeSchurMarkovScalar p : Complex) •
        ((suffixEulerFrameReverseTransition lambda p S)† ∘L
            suffixActualBandCompleteBoundaryResponse owner lambda S -
          suffixActualBandCompleteBoundaryResponse owner lambda (p :: S) ∘L
            (suffixEulerFrameReverseTransition lambda p S)†)) := by
  let data := suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis pairedBoundaryBasis hfactor
  have hdata : data.traceProduct =
      suffixActualBandLocalRawDefect owner lambda p S := by
    exact suffixActualBandLocalRawDefectPairData_traceProduct_eq owner lambda p S
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor
  calc
    (suffixActualBandLocalRawDefectPairData owner lambda p S a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis pairedBoundaryBasis hfactor).swap.traceProduct ∘L
          (suffixEulerFrameReverseTransition lambda p S)† =
        suffixActualBandCompleteSwappedLocalCofactor owner lambda p S := by
      simpa only [data] using
        (swappedLocalPair_traceProduct_comp_reverseAdjoint_eq_completeCofactor
          owner lambda p S sourceBasis data hdata)
    _ = -((primeSchurMarkovScalar p : Complex) •
        ((suffixEulerFrameReverseTransition lambda p S)† ∘L
            suffixActualBandCompleteBoundaryResponse owner lambda S -
          suffixActualBandCompleteBoundaryResponse owner lambda (p :: S) ∘L
            (suffixEulerFrameReverseTransition lambda p S)†)) :=
      suffixActualBandCompleteSwappedLocalCofactor_eq_coupledBoundaryLedger
        owner lambda p S

/-! ## Exact boundary of the finite radial-column route -/

/-- A bounded readout from Proof 639's first `N` weighted radial blocks to the
complete swapped cofactor.  This is an additional source premise, not a field
constructed by the local Hilbert--Schmidt pair. -/
structure SuffixSwappedLocalCofactorFiniteRadialReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat) (bound : Real) where
  bound_nonneg : 0 <= bound
  readout : PiLp 2 (fun _ : Fin N => finiteSCarrier) →L[ℂ]
    sourceSoninCarrier lambda
  readout_norm_le : ‖readout‖ <= bound
  factorization :
    readout ∘L finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N =
      suffixActualBandCompleteSwappedLocalCofactor owner lambda p S

/-- Pointwise relative-energy form of the missing finite radial-column
factorization. -/
def SuffixSwappedLocalCofactorFiniteRadialDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat) (bound : Real) : Prop :=
  0 <= bound ∧ forall x : sourceSoninCarrier lambda,
    ‖suffixActualBandCompleteSwappedLocalCofactor owner lambda p S x‖ ^ 2 <=
      bound ^ 2 *
        ‖finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x‖ ^ 2

/-- Douglas constructs the finite radial readout from precisely the full
same-vector domination. -/
noncomputable def finiteRadialReadoutDataOfDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat} {bound : Real}
    (hdom : SuffixSwappedLocalCofactorFiniteRadialDomination
      owner lambda p S N bound) :
    SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound := by
  let witness := exists_factor_of_norm_sq_le
    (suffixActualBandCompleteSwappedLocalCofactor owner lambda p S)
    (finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N)
    bound hdom.1 hdom.2
  let readout := Classical.choose witness
  have readoutSpec := Classical.choose_spec witness
  exact
    { bound_nonneg := hdom.1
      readout := readout
      readout_norm_le := readoutSpec.1
      factorization := readoutSpec.2 }

/-- Every finite radial readout gives the corresponding full-source
relative-energy estimate. -/
theorem finiteRadialDominationOfReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat} {bound : Real}
    (data : SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound) :
    SuffixSwappedLocalCofactorFiniteRadialDomination
      owner lambda p S N bound := by
  refine ⟨data.bound_nonneg, ?_⟩
  intro x
  have hpoint := DFunLike.congr_fun data.factorization x
  have hnorm :
      ‖suffixActualBandCompleteSwappedLocalCofactor owner lambda p S x‖ <=
        bound *
          ‖finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x‖ := by
    rw [← hpoint]
    calc
      ‖data.readout
          (finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x)‖ <=
          ‖data.readout‖ *
            ‖finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x‖ :=
        data.readout.le_opNorm _
      _ <= bound *
          ‖finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x‖ :=
        mul_le_mul_of_nonneg_right data.readout_norm_le (norm_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg data.bound_nonneg (norm_nonneg _))).2 hnorm

/-- Existence of the finite radial readout is exactly the new relative-energy
premise.  Proof 639 does not establish either side. -/
theorem exists_finiteRadialReadout_iff_domination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat) (bound : Real) :
    Nonempty (SuffixSwappedLocalCofactorFiniteRadialReadoutData
        owner lambda p S N bound) <->
      SuffixSwappedLocalCofactorFiniteRadialDomination
        owner lambda p S N bound := by
  constructor
  · rintro ⟨data⟩
    exact finiteRadialDominationOfReadoutData data
  · intro hdom
    exact ⟨finiteRadialReadoutDataOfDomination hdom⟩

/-- Necessary kernel condition for any finite-column collapse.  This is the
concrete obstruction left open by the current source: every vector invisible
to the selected finite radial blocks must also be invisible to the complete
coupled cofactor. -/
theorem completeSwappedLocalCofactor_eq_zero_of_finiteRadialColumn_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat} {bound : Real}
    (data : SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound)
    (x : sourceSoninCarrier lambda)
    (hx : finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x = 0) :
    suffixActualBandCompleteSwappedLocalCofactor owner lambda p S x = 0 := by
  have hpoint := DFunLike.congr_fun data.factorization x
  simpa only [ContinuousLinearMap.comp_apply, hx, map_zero] using hpoint.symm

/-! ## Conditional handoff to the raw Bone 1 column -/

/-- The exact source readout obtained by composing a supplied finite radial
cofactor readout with Proof 639's column readout and the Schur cofactor. -/
noncomputable def
    SuffixSwappedLocalCofactorFiniteRadialReadoutData.rawAmbientReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat} {bound : Real}
    (data : SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  (-((primeSchurMarkovScalar p : Complex)⁻¹)) •
    ((suffixEulerFrameTransition lambda p S)† ∘L data.readout ∘L
      finitePrimeEulerRadialGeometricReadoutColumn lambda p N)

/-- The conditional readout reconstructs the complete signed interior from
the raw right-co-defect column exactly. -/
theorem
    SuffixSwappedLocalCofactorFiniteRadialReadoutData.rawAmbientReadout_comp_rawColumn
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat} {bound : Real}
    (data : SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound) :
    data.rawAmbientReadout ∘L newFrameAntiresonantColumn lambda p S =
      signedCompressedInteriorOwner owner lambda p S := by
  have hcolumn := finiteRadialGeometricReadoutColumn_comp_ambientLossColumn
    lambda p S N
  have howner :=
    signedCompressedInteriorOwner_eq_neg_scalarInv_smul_transitionAdjoint_comp_localRawDefectAdjoint_comp_reverseAdjoint
      owner lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hcolumnPoint := DFunLike.congr_fun hcolumn x
  have hfactorPoint := DFunLike.congr_fun data.factorization x
  have hownerPoint := DFunLike.congr_fun howner x
  simp only [SuffixSwappedLocalCofactorFiniteRadialReadoutData.rawAmbientReadout,
    suffixActualBandCompleteSwappedLocalCofactor,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
    at hcolumnPoint hfactorPoint hownerPoint ⊢
  rw [hcolumnPoint, hfactorPoint]
  exact hownerPoint

/-- The supplied finite-column factor gives an explicit raw-column pointwise
bound.  The costs are `8` from `rho_p^-1` and `32` from Proof 639. -/
theorem norm_signedCompressedInteriorOwner_le_twoFiftySix_mul_finiteRadialBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat} {bound : Real}
    (data : SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound)
    (x : sourceSoninCarrier lambda) :
    ‖signedCompressedInteriorOwner owner lambda p S x‖ <=
      (256 * bound) * ‖newFrameAntiresonantColumn lambda p S x‖ := by
  have hfactor := DFunLike.congr_fun data.factorization x
  have howner := DFunLike.congr_fun
    (signedCompressedInteriorOwner_eq_neg_scalarInv_smul_transitionAdjoint_comp_localRawDefectAdjoint_comp_reverseAdjoint
      owner lambda p S) x
  have htransition : ‖(suffixEulerFrameTransition lambda p S)†‖ <= 1 := by
    calc
      ‖(suffixEulerFrameTransition lambda p S)†‖ =
          ‖suffixEulerFrameTransition lambda p S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ <= 1 := suffixEulerFrameTransition_norm_le_one lambda p S
  have hboundary :=
    norm_finitePrimeEulerRadialGeometricBoundaryColumn_apply_le
      lambda p S N x
  calc
    ‖signedCompressedInteriorOwner owner lambda p S x‖ =
        ‖((primeSchurMarkovScalar p : Complex)⁻¹)‖ *
          ‖(suffixEulerFrameTransition lambda p S)†
            (suffixActualBandCompleteSwappedLocalCofactor
              owner lambda p S x)‖ := by
      rw [howner]
      simp only [suffixActualBandCompleteSwappedLocalCofactor,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        norm_smul, norm_neg]
    _ <= 8 *
          ‖(suffixEulerFrameTransition lambda p S)†
            (suffixActualBandCompleteSwappedLocalCofactor
              owner lambda p S x)‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_primeSchurMarkovScalar_inv_le_eight p) (norm_nonneg _)
    _ <= 8 *
          ‖suffixActualBandCompleteSwappedLocalCofactor
            owner lambda p S x‖ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        ‖(suffixEulerFrameTransition lambda p S)†
            (suffixActualBandCompleteSwappedLocalCofactor
              owner lambda p S x)‖ <=
            ‖(suffixEulerFrameTransition lambda p S)†‖ *
              ‖suffixActualBandCompleteSwappedLocalCofactor
                owner lambda p S x‖ :=
          (suffixEulerFrameTransition lambda p S)†.le_opNorm _
        _ <= 1 *
              ‖suffixActualBandCompleteSwappedLocalCofactor
                owner lambda p S x‖ :=
          mul_le_mul_of_nonneg_right htransition (norm_nonneg _)
        _ = ‖suffixActualBandCompleteSwappedLocalCofactor
                owner lambda p S x‖ := one_mul _
    _ = 8 *
          ‖data.readout
            (finitePrimeEulerRadialGeometricBoundaryColumn
              lambda p S N x)‖ := by
      rw [← hfactor]
      rfl
    _ <= 8 * (bound *
          ‖finitePrimeEulerRadialGeometricBoundaryColumn
            lambda p S N x‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        ‖data.readout
            (finitePrimeEulerRadialGeometricBoundaryColumn
              lambda p S N x)‖ <=
            ‖data.readout‖ *
              ‖finitePrimeEulerRadialGeometricBoundaryColumn
                lambda p S N x‖ := data.readout.le_opNorm _
        _ <= bound *
              ‖finitePrimeEulerRadialGeometricBoundaryColumn
                lambda p S N x‖ :=
          mul_le_mul_of_nonneg_right data.readout_norm_le (norm_nonneg _)
    _ <= 8 * (bound *
          (32 * ‖newFrameAntiresonantColumn lambda p S x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hboundary data.bound_nonneg
    _ = (256 * bound) *
          ‖newFrameAntiresonantColumn lambda p S x‖ := by ring

/-- Squared-energy form matching the active raw Bone 1 denominator. -/
theorem normSq_signedCompressedInteriorOwner_le_twoFiftySix_mul_finiteRadialBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat} {bound : Real}
    (data : SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound)
    (x : sourceSoninCarrier lambda) :
    ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 <=
      (256 * bound) ^ 2 *
        ‖newFrameAntiresonantColumn lambda p S x‖ ^ 2 := by
  have hnorm :=
    norm_signedCompressedInteriorOwner_le_twoFiftySix_mul_finiteRadialBound
      data x
  have hbound : 0 <= 256 * bound :=
    mul_nonneg (by norm_num) data.bound_nonneg
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hbound (norm_nonneg _))).2 hnorm

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge
end CCM25Concrete
end Source
end ConnesWeilRH
