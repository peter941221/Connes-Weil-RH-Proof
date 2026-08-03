/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawRenewalBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedIndexBridge

/-!
# Support-first split of the raw physical renewal response

The raw Gate endpoint is the inverse-lower-factor physical renewal response.
This module inserts a two-sided displacement clip directly into that complete
operator-valued renewal expansion.  It proves an exact compact-displacement
plus tail decomposition before a trace, real part, or absolute value occurs.

The transported Sonin projection remains between the two translations inside
each physical atom.  Thus the split does not assert that the tail vanishes:
the missing source theorem must establish that fact for the complete physical
trace, rather than treating the coefficient support law as an operator law.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawRenewalSupportSplit

open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSForwardRenewal
open CCM24FiniteSGramResponse
open CCM24FiniteSMultiRenewal
open CCM24FiniteSPhysicalRenewalExpansion
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCausalMarkovRawRenewalBridge
open CCM24FiniteSTwoSidedIndexBridge
open CCM24FiniteSTwoSidedOperatorExpansion
open CCM24FiniteSTwoSidedRenewal

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- One raw physical renewal atom.  The family-level inverse lower-factor
square is placed on every atom only for this support-first operator split;
the original response is recovered by summing these atoms exactly. -/
noncomputable def finiteEulerPhysicalRawRenewalAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  ((finiteEulerLowerFactor family.visiblePrimes : Complex) ^ 2)⁻¹ •
    finiteEulerPhysicalResponseAtom owner lambda family forwardIndex renewalIndex

/-- The physical operator underlying one paired renewal coefficient.  The
forward and renewal translations remain on their respective sides of the
actual transported Sonin projection. -/
noncomputable def finiteEulerPhysicalUnweightedRenewalAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  -((sourceInclusion lambda)†) ∘L detectorOperator owner ∘L
    (ContinuousLinearMap.id Complex finiteSCarrier - sourceSoninProjection lambda) ∘L
    (cc20GlobalLogTranslation
      (finiteEulerForwardDisplacement family.visiblePrimes forwardIndex)).toContinuousLinearMap ∘L
    transportedSoninProjection lambda family ∘L
    (cc20GlobalLogTranslation
      (finiteEulerRenewalDisplacement family.visiblePrimes renewalIndex)).toContinuousLinearMap ∘L
    sourceInclusion lambda

/-- The normalized physical atom is its signed paired coefficient times the
unweighted two-translation kernel. -/
theorem finiteEulerPhysicalResponseAtom_eq_signedCoefficient_smul_unweighted
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    finiteEulerPhysicalResponseAtom owner lambda family forwardIndex renewalIndex =
      (finiteEulerProjectionSandwichSignedWeight family.visiblePrimes forwardIndex
        renewalIndex : Complex) •
        finiteEulerPhysicalUnweightedRenewalAtom owner lambda family forwardIndex
          renewalIndex := by
  unfold finiteEulerPhysicalResponseAtom finiteEulerPhysicalLeakageAtom
    finiteEulerProjectionSandwichTerm finiteEulerForwardOperatorTerm
    finiteEulerRenewalAdjointOperatorTerm
    finiteEulerPhysicalUnweightedRenewalAtom
  have hscalar :
      (finiteEulerRenewalWeight family.visiblePrimes renewalIndex : Complex) *
          (finiteEulerForwardSignedWeight family.visiblePrimes forwardIndex : Complex) =
        (finiteEulerProjectionSandwichSignedWeight family.visiblePrimes forwardIndex
          renewalIndex : Complex) := by
    simp only [finiteEulerProjectionSandwichSignedWeight, Complex.ofReal_mul]
    ring
  rw [← hscalar]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, map_smul,
    map_neg, smul_smul]
  ring

/-- The raw atom carries the raw two-sided signed coefficient exactly. -/
theorem finiteEulerPhysicalRawRenewalAtom_eq_rawCoefficient_smul_unweighted
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    finiteEulerPhysicalRawRenewalAtom owner lambda family forwardIndex renewalIndex =
      (finiteEulerProjectionSandwichRawSignedWeight family.visiblePrimes forwardIndex
        renewalIndex : Complex) •
        finiteEulerPhysicalUnweightedRenewalAtom owner lambda family forwardIndex
          renewalIndex := by
  rw [finiteEulerPhysicalRawRenewalAtom,
    finiteEulerPhysicalResponseAtom_eq_signedCoefficient_smul_unweighted]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  unfold finiteEulerProjectionSandwichRawSignedWeight
  have hfactor : (finiteEulerLowerFactor family.visiblePrimes : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))
  push_cast
  field_simp [hfactor]

/-- The raw atom is summable in operator norm for every fixed forward index.
This is a fixed-family analytic fact only; no trace is interchanged here. -/
theorem summable_finiteEulerPhysicalRawRenewalAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable (fun renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes =>
      finiteEulerPhysicalRawRenewalAtom owner lambda family forwardIndex
        renewalIndex) := by
  exact Summable.const_smul _
    (summable_finiteEulerPhysicalResponseAtom owner lambda family forwardIndex)

/-- The raw response is the finite-plus-countable sum of its raw atoms. -/
theorem inverseLowerFactorPhysicalRenewalResponse_eq_sum_rawAtoms
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    inverseLowerFactorPhysicalRenewalResponse owner lambda family =
      ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerPhysicalRawRenewalAtom owner lambda family forwardIndex
            renewalIndex := by
  unfold inverseLowerFactorPhysicalRenewalResponse
    finiteEulerPhysicalRawRenewalAtom
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro forwardIndex _
  exact (Summable.tsum_const_smul
    ((finiteEulerLowerFactor family.visiblePrimes : Complex) ^ 2)⁻¹
    (summable_finiteEulerPhysicalResponseAtom owner lambda family forwardIndex)).symm

/-- Compact-displacement part of one raw physical atom.  The condition uses
the paired forward/renewal displacement, while the atom itself retains the
actual intervening transported Sonin projection. -/
noncomputable def finiteEulerPhysicalRawRenewalSupportAtom
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  if finiteEulerTwoSidedDisplacement family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) <= B then
    finiteEulerPhysicalRawRenewalAtom owner lambda family forwardIndex renewalIndex
  else 0

/-- Complementary tail of one raw physical atom. -/
noncomputable def finiteEulerPhysicalRawRenewalTailAtom
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  if finiteEulerTwoSidedDisplacement family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) <= B then
    0
  else finiteEulerPhysicalRawRenewalAtom owner lambda family forwardIndex renewalIndex

/-- The two support pieces recover each raw atom without changing its sign or
moving any operator factor. -/
theorem finiteEulerPhysicalRawRenewalAtom_eq_support_add_tail
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    finiteEulerPhysicalRawRenewalAtom owner lambda family forwardIndex renewalIndex =
      finiteEulerPhysicalRawRenewalSupportAtom B owner lambda family forwardIndex
          renewalIndex +
        finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
          renewalIndex := by
  unfold finiteEulerPhysicalRawRenewalSupportAtom
    finiteEulerPhysicalRawRenewalTailAtom
  split_ifs <;> simp

/-- Both support pieces inherit fixed-family operator-norm summability. -/
theorem summable_finiteEulerPhysicalRawRenewalSupportAtom
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable (fun renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes =>
      finiteEulerPhysicalRawRenewalSupportAtom B owner lambda family forwardIndex
        renewalIndex) := by
  classical
  let support : Set (FiniteEulerRenewalIndex family.visiblePrimes) :=
    {renewalIndex | finiteEulerTwoSidedDisplacement family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) ≤ B}
  apply (summable_finiteEulerPhysicalRawRenewalAtom owner lambda family
    forwardIndex).indicator support |>.congr
  intro renewalIndex
  by_cases hdisplacement : finiteEulerTwoSidedDisplacement family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) ≤ B <;>
    simp [support, finiteEulerPhysicalRawRenewalSupportAtom, hdisplacement]

theorem summable_finiteEulerPhysicalRawRenewalTailAtom
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable (fun renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes =>
      finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
        renewalIndex) := by
  classical
  let support : Set (FiniteEulerRenewalIndex family.visiblePrimes) :=
    {renewalIndex | finiteEulerTwoSidedDisplacement family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) ≤ B}
  apply (summable_finiteEulerPhysicalRawRenewalAtom owner lambda family
    forwardIndex).indicator supportᶜ |>.congr
  intro renewalIndex
  by_cases hdisplacement : finiteEulerTwoSidedDisplacement family.visiblePrimes
      (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) ≤ B <;>
    simp [support, finiteEulerPhysicalRawRenewalTailAtom, hdisplacement]

/-- The full support-truncated raw renewal response. -/
noncomputable def inverseLowerFactorPhysicalRenewalSupportResponse
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
    ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
      finiteEulerPhysicalRawRenewalSupportAtom B owner lambda family forwardIndex
        renewalIndex

/-- The full complementary raw renewal tail. -/
noncomputable def inverseLowerFactorPhysicalRenewalTailResponse
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
    ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
      finiteEulerPhysicalRawRenewalTailAtom B owner lambda family forwardIndex
        renewalIndex

/-- Exact support-first decomposition of the raw Gate endpoint, at operator
level and before any trace.  Compact root support may only delete the tail
after a theorem about this complete physical owner is proved. -/
theorem inverseLowerFactorPhysicalRenewalResponse_eq_support_add_tail
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    inverseLowerFactorPhysicalRenewalResponse owner lambda family =
      inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family +
        inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family := by
  rw [inverseLowerFactorPhysicalRenewalResponse_eq_sum_rawAtoms]
  unfold inverseLowerFactorPhysicalRenewalSupportResponse
    inverseLowerFactorPhysicalRenewalTailResponse
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro forwardIndex _
  rw [<- Summable.tsum_add
    (summable_finiteEulerPhysicalRawRenewalSupportAtom B owner lambda family
      forwardIndex)
    (summable_finiteEulerPhysicalRawRenewalTailAtom B owner lambda family
      forwardIndex)]
  apply tsum_congr
  intro renewalIndex
  exact finiteEulerPhysicalRawRenewalAtom_eq_support_add_tail B owner lambda
    family forwardIndex renewalIndex

/-- The raw coefficient associated with a clipped physical atom is exactly
the existing two-sided raw coefficient after the paired-index identification.
This is a coefficient identity only; it does not turn displacement support
into trace support across the transported Sonin projection. -/
theorem abs_rawPhysicalRenewalCoefficient_eq_twoSidedRawWeight
    (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    abs (finiteEulerProjectionSandwichRawSignedWeight family.visiblePrimes
      forwardIndex renewalIndex) =
      finiteEulerTwoSidedRawWeight family.visiblePrimes
        (pairForwardRenewalIndex family.visiblePrimes (forwardIndex, renewalIndex)) :=
  abs_finiteEulerProjectionSandwichRawSignedWeight family.visiblePrimes
    forwardIndex renewalIndex

end CCM24FiniteSCausalMarkovRawRenewalSupportSplit
end CCM25Concrete
end Source
end ConnesWeilRH
