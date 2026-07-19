/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedOperatorExpansion
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSupportMajorant

/-!
# Index bridge for the two-sided Euler sandwich

The operator expansion naturally has a forward Boolean multi-index and an
inverse geometric multi-index.  The scalar majorant uses one paired coordinate
`(Bool × Nat)` per prime.  This module proves that the two indexings are
equivalent and that both the total displacement and absolute coefficient agree
exactly.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSTwoSidedIndexBridge

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalMarkov
open CCM24FiniteSMultiRenewal
open CCM24FiniteSSupportMajorant
open CCM24FiniteSTwoSidedRenewal
open CCM24FiniteSForwardRenewal
open CCM24FiniteSTwoSidedOperatorExpansion

/-- Pair the forward and inverse coordinates prime by prime. -/
def pairForwardRenewalIndex :
    (S : List CCM24VisiblePrime) →
      FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S →
        FiniteEulerTwoSidedRenewalIndex S
  | [], _ => PUnit.unit
  | _ :: S, index =>
      ((index.1.1, index.2.1),
        pairForwardRenewalIndex S (index.1.2, index.2.2))

/-- Split a paired two-sided coordinate into its forward and inverse parts. -/
def splitForwardRenewalIndex :
    (S : List CCM24VisiblePrime) →
      FiniteEulerTwoSidedRenewalIndex S →
        FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S
  | [], _ => (PUnit.unit, PUnit.unit)
  | _ :: S, index =>
      let tail := splitForwardRenewalIndex S index.2
      ((index.1.1, tail.1), (index.1.2, tail.2))

theorem split_pairForwardRenewalIndex
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S) :
    splitForwardRenewalIndex S (pairForwardRenewalIndex S index) = index := by
  induction S with
  | nil =>
      rcases index with ⟨forwardIndex, renewalIndex⟩
      cases forwardIndex
      cases renewalIndex
      rfl
  | cons p S ih =>
      rcases index with ⟨⟨choice, forwardTail⟩, ⟨count, renewalTail⟩⟩
      simp only [pairForwardRenewalIndex, splitForwardRenewalIndex]
      rw [ih (forwardTail, renewalTail)]

theorem pair_splitForwardRenewalIndex
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    pairForwardRenewalIndex S (splitForwardRenewalIndex S index) = index := by
  induction S with
  | nil =>
      cases index
      rfl
  | cons p S ih =>
      rcases index with ⟨⟨choice, count⟩, tail⟩
      simp only [splitForwardRenewalIndex, pairForwardRenewalIndex]
      rw [ih tail]

/-- Equivalence between the operator and scalar two-sided indexings. -/
def forwardRenewalIndexEquiv (S : List CCM24VisiblePrime) :
    (FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S) ≃
      FiniteEulerTwoSidedRenewalIndex S where
  toFun := pairForwardRenewalIndex S
  invFun := splitForwardRenewalIndex S
  left_inv := split_pairForwardRenewalIndex S
  right_inv := pair_splitForwardRenewalIndex S

/-- The operator pair's two displacements add to the scalar majorant's total
displacement. -/
theorem finiteEulerTwoSidedDisplacement_pair
    (S : List CCM24VisiblePrime)
    (forwardIndex : FiniteEulerForwardIndex S)
    (renewalIndex : FiniteEulerRenewalIndex S) :
    finiteEulerTwoSidedDisplacement S
        (pairForwardRenewalIndex S (forwardIndex, renewalIndex)) =
      finiteEulerForwardDisplacement S forwardIndex +
        finiteEulerRenewalDisplacement S renewalIndex := by
  induction S with
  | nil =>
      cases forwardIndex
      cases renewalIndex
      simp [finiteEulerTwoSidedDisplacement,
        finiteEulerForwardDisplacement, finiteEulerRenewalDisplacement]
  | cons p S ih =>
      rcases forwardIndex with ⟨choice, forwardTail⟩
      rcases renewalIndex with ⟨count, renewalTail⟩
      simp only [pairForwardRenewalIndex,
        finiteEulerTwoSidedDisplacement, primeTwoSidedDisplacement,
        finiteEulerForwardDisplacement, primeForwardDisplacement,
        finiteEulerRenewalDisplacement]
      rw [ih forwardTail renewalTail]
      push_cast
      ring

/-- The signed scalar coefficient carried by one projection-sandwich atom. -/
noncomputable def finiteEulerProjectionSandwichSignedWeight
    (S : List CCM24VisiblePrime) (forwardIndex : FiniteEulerForwardIndex S)
    (renewalIndex : FiniteEulerRenewalIndex S) : ℝ :=
  finiteEulerForwardSignedWeight S forwardIndex *
    finiteEulerRenewalWeight S renewalIndex

theorem abs_primeForwardSignedWeight_mul_renewal
    (p : CCM24VisiblePrime) (choice : Bool) (count : ℕ) :
    |primeForwardSignedWeight p choice| *
        primeEulerRenewalWeight p count =
      primeTwoSidedNormalizedWeight p (choice, count) := by
  have hlower : 0 ≤ 1 - ccm24PrimeEulerCoefficient p :=
    le_of_lt (primeEulerLowerFactor_pos p)
  have hcoeff := ccm24PrimeEulerCoefficient_nonneg p
  cases choice <;>
    simp [primeForwardSignedWeight, primeEulerRenewalWeight,
      primeTwoSidedNormalizedWeight, primeTwoSidedRawWeight,
      forwardEulerExponent, abs_of_nonneg, abs_mul, hlower, hcoeff,
      abs_neg] <;>
    ring

/-- Absolute signed operator weight equals the normalized two-sided scalar
weight under the coordinate equivalence. -/
theorem abs_finiteEulerProjectionSandwichSignedWeight
    (S : List CCM24VisiblePrime)
    (forwardIndex : FiniteEulerForwardIndex S)
    (renewalIndex : FiniteEulerRenewalIndex S) :
    |finiteEulerProjectionSandwichSignedWeight S forwardIndex renewalIndex| =
      finiteEulerTwoSidedNormalizedWeight S
        (pairForwardRenewalIndex S (forwardIndex, renewalIndex)) := by
  induction S with
  | nil =>
      cases forwardIndex
      cases renewalIndex
      simp [finiteEulerProjectionSandwichSignedWeight,
        finiteEulerForwardSignedWeight, finiteEulerRenewalWeight,
        finiteEulerTwoSidedNormalizedWeight]
  | cons p S ih =>
      rcases forwardIndex with ⟨choice, forwardTail⟩
      rcases renewalIndex with ⟨count, renewalTail⟩
      simp only [finiteEulerProjectionSandwichSignedWeight,
        finiteEulerForwardSignedWeight, finiteEulerRenewalWeight,
        finiteEulerTwoSidedNormalizedWeight, pairForwardRenewalIndex]
      rw [show primeForwardSignedWeight p choice *
          finiteEulerForwardSignedWeight S forwardTail *
            (primeEulerRenewalWeight p count *
              finiteEulerRenewalWeight S renewalTail) =
          (primeForwardSignedWeight p choice *
            primeEulerRenewalWeight p count) *
              (finiteEulerForwardSignedWeight S forwardTail *
                finiteEulerRenewalWeight S renewalTail) by ring]
      rw [abs_mul
          (primeForwardSignedWeight p choice *
            primeEulerRenewalWeight p count)
          (finiteEulerForwardSignedWeight S forwardTail *
            finiteEulerRenewalWeight S renewalTail),
        abs_mul (primeForwardSignedWeight p choice)
          (primeEulerRenewalWeight p count),
        abs_of_nonneg (primeEulerRenewalWeight_nonneg p count),
        abs_primeForwardSignedWeight_mul_renewal]
      change primeTwoSidedNormalizedWeight p (choice, count) *
          |finiteEulerProjectionSandwichSignedWeight S forwardTail
            renewalTail| = _
      rw [ih forwardTail renewalTail]

/-!
The operator expansion above is normalized twice: once on the forward Euler
polynomial and once on the causal inverse.  Gate 3U is a raw statement, so its
coefficient must divide by the square of the same lower factor before any
support estimate is applied.  Keeping this as a named coefficient prevents a
normalized total-variation bound from being silently reused as a raw one.
-/

noncomputable def finiteEulerProjectionSandwichRawSignedWeight
    (S : List CCM24VisiblePrime)
    (forwardIndex : FiniteEulerForwardIndex S)
    (renewalIndex : FiniteEulerRenewalIndex S) : ℝ :=
  finiteEulerProjectionSandwichSignedWeight S forwardIndex renewalIndex /
    (finiteEulerLowerFactor S) ^ 2

theorem finiteEulerTwoSidedNormalizedWeight_eq_lowerFactor_sq_mul_rawWeight
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    finiteEulerTwoSidedNormalizedWeight S index =
      (finiteEulerLowerFactor S) ^ 2 *
        finiteEulerTwoSidedRawWeight S index := by
  induction S with
  | nil =>
      cases index
      simp [finiteEulerTwoSidedNormalizedWeight,
        finiteEulerTwoSidedRawWeight, finiteEulerLowerFactor]
  | cons p S ih =>
      rcases index with ⟨head, tail⟩
      simp only [finiteEulerTwoSidedNormalizedWeight,
        finiteEulerTwoSidedRawWeight, finiteEulerLowerFactor,
        List.map_cons, List.prod_cons]
      rw [ih tail]
      simp [primeTwoSidedNormalizedWeight, finiteEulerLowerFactor]
      ring

/-! The raw coefficient has exactly the positive two-sided raw variation. -/
theorem abs_finiteEulerProjectionSandwichRawSignedWeight
    (S : List CCM24VisiblePrime)
    (forwardIndex : FiniteEulerForwardIndex S)
    (renewalIndex : FiniteEulerRenewalIndex S) :
    |finiteEulerProjectionSandwichRawSignedWeight S forwardIndex
        renewalIndex| =
      finiteEulerTwoSidedRawWeight S
        (pairForwardRenewalIndex S (forwardIndex, renewalIndex)) := by
  have hlower : 0 < finiteEulerLowerFactor S :=
    finiteEulerLowerFactor_pos S
  rw [finiteEulerProjectionSandwichRawSignedWeight, abs_div,
    abs_finiteEulerProjectionSandwichSignedWeight,
    finiteEulerTwoSidedNormalizedWeight_eq_lowerFactor_sq_mul_rawWeight]
  rw [abs_of_pos (sq_pos_of_pos hlower)]
  field_simp [ne_of_gt hlower]

/-! The compact raw coefficient is the coefficient-layer input to the
source-specific boundary producer.  It is deliberately separate from the
trace of the projection sandwich: coefficient support alone does not imply
that trace support. -/
noncomputable def finiteEulerProjectionSandwichCompactRawSignedWeight
    (B : ℝ) (S : List CCM24VisiblePrime)
    (forwardIndex : FiniteEulerForwardIndex S)
    (renewalIndex : FiniteEulerRenewalIndex S) : ℝ :=
  if finiteEulerTwoSidedDisplacement S
        (pairForwardRenewalIndex S (forwardIndex, renewalIndex)) ≤ B then
    finiteEulerProjectionSandwichRawSignedWeight S forwardIndex renewalIndex
  else 0

theorem abs_finiteEulerProjectionSandwichCompactRawSignedWeight
    (B : ℝ) (S : List CCM24VisiblePrime)
    (forwardIndex : FiniteEulerForwardIndex S)
    (renewalIndex : FiniteEulerRenewalIndex S) :
    |finiteEulerProjectionSandwichCompactRawSignedWeight B S forwardIndex
        renewalIndex| =
      finiteEulerTwoSidedCompactRawWeight B S
        (pairForwardRenewalIndex S (forwardIndex, renewalIndex)) := by
  unfold finiteEulerProjectionSandwichCompactRawSignedWeight
    finiteEulerTwoSidedCompactRawWeight
  split_ifs with hdisp
  · rw [abs_finiteEulerProjectionSandwichRawSignedWeight]
  · simp

theorem tsum_abs_finiteEulerProjectionSandwichCompactRawSignedWeight_le_universal
    (B : ℝ) (S : List CCM24VisiblePrime) (hS : S.Nodup) :
    ∑' index : FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S,
        |finiteEulerProjectionSandwichCompactRawSignedWeight B S
            index.1 index.2| ≤
      (7 : ℝ) ^ (Nat.ceil (Real.exp B) + 1) := by
  calc
    ∑' index : FiniteEulerForwardIndex S × FiniteEulerRenewalIndex S,
        |finiteEulerProjectionSandwichCompactRawSignedWeight B S
            index.1 index.2| =
      ∑' index : FiniteEulerTwoSidedRenewalIndex S,
        finiteEulerTwoSidedCompactRawWeight B S index := by
      rw [← (forwardRenewalIndexEquiv S).tsum_eq]
      apply tsum_congr
      intro index
      exact abs_finiteEulerProjectionSandwichCompactRawSignedWeight B S
        index.1 index.2
    _ ≤ (7 : ℝ) ^ (Nat.ceil (Real.exp B) + 1) :=
      tsum_finiteEulerTwoSidedCompactRawWeight_le_universal B S hS

end CCM24FiniteSTwoSidedIndexBridge
end CCM25Concrete
end Source
end ConnesWeilRH
