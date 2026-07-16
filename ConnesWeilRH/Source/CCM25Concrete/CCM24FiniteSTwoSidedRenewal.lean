/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedCausalCoframe

/-!
# Two-sided finite Euler renewal law

The forward normalized Euler polynomial contributes a Boolean choice at each
visible prime, while the normalized inverse contributes a geometric count.
The combined displacement is always causal.  Its absolute normalized mass is
`prod_p (1-p⁻¹)`, hence at most one.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSTwoSidedRenewal

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalMarkov

/-- The exponent contributed by one forward Euler choice. -/
def forwardEulerExponent (choice : Bool) : ℕ :=
  if choice then 1 else 0

/-- One forward/inverse coordinate at a visible prime. -/
abbrev PrimeTwoSidedRenewalIndex := Bool × ℕ

/-- Absolute coefficient before the two lower factors are inserted. -/
noncomputable def primeTwoSidedRawWeight
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) : ℝ :=
  ccm24PrimeEulerCoefficient p ^
    (forwardEulerExponent index.1 + index.2)

/-- Absolute coefficient after both lower factors are inserted. -/
noncomputable def primeTwoSidedNormalizedWeight
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) : ℝ :=
  (1 - ccm24PrimeEulerCoefficient p) ^ 2 *
    primeTwoSidedRawWeight p index

/-- Causal displacement of one forward/inverse coordinate. -/
noncomputable def primeTwoSidedDisplacement
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) : ℝ :=
  ((forwardEulerExponent index.1 + index.2 : ℕ) : ℝ) * Real.log p

theorem primeTwoSidedRawWeight_nonneg
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    0 ≤ primeTwoSidedRawWeight p index :=
  pow_nonneg (ccm24PrimeEulerCoefficient_nonneg p) _

theorem primeTwoSidedNormalizedWeight_nonneg
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    0 ≤ primeTwoSidedNormalizedWeight p index := by
  exact mul_nonneg (sq_nonneg _) (primeTwoSidedRawWeight_nonneg p index)

theorem primeTwoSidedDisplacement_nonneg
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    0 ≤ primeTwoSidedDisplacement p index := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast p.property.le))

theorem summable_primeTwoSidedRawWeight (p : CCM24VisiblePrime) :
    Summable (primeTwoSidedRawWeight p) := by
  rw [summable_prod_of_nonneg]
  · constructor
    · intro choice
      unfold primeTwoSidedRawWeight
      simp only [pow_add]
      exact (summable_geometric_of_norm_lt_one
        (show ‖ccm24PrimeEulerCoefficient p‖ < 1 by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
          exact ccm24PrimeEulerCoefficient_lt_one p)).mul_left _
    · exact (hasSum_fintype _).summable
  · intro index
    exact primeTwoSidedRawWeight_nonneg p index

/-- The raw total variation at one prime is `(1+a_p)/(1-a_p)`. -/
theorem tsum_primeTwoSidedRawWeight (p : CCM24VisiblePrime) :
    ∑' index : PrimeTwoSidedRenewalIndex,
      primeTwoSidedRawWeight p index =
        (1 + ccm24PrimeEulerCoefficient p) /
          (1 - ccm24PrimeEulerCoefficient p) := by
  have hsum := summable_primeTwoSidedRawWeight p
  rw [Summable.tsum_prod hsum]
  simp only [primeTwoSidedRawWeight, pow_add]
  simp_rw [(summable_geometric_of_norm_lt_one
    (show ‖ccm24PrimeEulerCoefficient p‖ < 1 by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
      exact ccm24PrimeEulerCoefficient_lt_one p)).tsum_mul_left]
  rw [tsum_geometric_of_lt_one (ccm24PrimeEulerCoefficient_nonneg p)
    (ccm24PrimeEulerCoefficient_lt_one p)]
  simp [forwardEulerExponent]
  field_simp [ne_of_gt (primeEulerLowerFactor_pos p)]
  ring

theorem summable_primeTwoSidedNormalizedWeight
    (p : CCM24VisiblePrime) :
    Summable (primeTwoSidedNormalizedWeight p) := by
  exact (summable_primeTwoSidedRawWeight p).mul_left
    ((1 - ccm24PrimeEulerCoefficient p) ^ 2)

/-- The normalized total variation at one prime is `1-a_p²`. -/
theorem tsum_primeTwoSidedNormalizedWeight (p : CCM24VisiblePrime) :
    ∑' index : PrimeTwoSidedRenewalIndex,
      primeTwoSidedNormalizedWeight p index =
        1 - ccm24PrimeEulerCoefficient p ^ 2 := by
  simp only [primeTwoSidedNormalizedWeight]
  rw [(summable_primeTwoSidedRawWeight p).tsum_mul_left,
    tsum_primeTwoSidedRawWeight]
  field_simp [ne_of_gt (primeEulerLowerFactor_pos p)]
  ring

/-- One two-sided coordinate for every visible-prime occurrence. -/
abbrev FiniteEulerTwoSidedRenewalIndex : List CCM24VisiblePrime → Type
  | [] => PUnit
  | _ :: S => PrimeTwoSidedRenewalIndex ×
      FiniteEulerTwoSidedRenewalIndex S

noncomputable def finiteEulerTwoSidedRawWeight :
    (S : List CCM24VisiblePrime) → FiniteEulerTwoSidedRenewalIndex S → ℝ
  | [], _ => 1
  | p :: S, index =>
      primeTwoSidedRawWeight p index.1 *
        finiteEulerTwoSidedRawWeight S index.2

noncomputable def finiteEulerTwoSidedNormalizedWeight :
    (S : List CCM24VisiblePrime) → FiniteEulerTwoSidedRenewalIndex S → ℝ
  | [], _ => 1
  | p :: S, index =>
      primeTwoSidedNormalizedWeight p index.1 *
        finiteEulerTwoSidedNormalizedWeight S index.2

noncomputable def finiteEulerTwoSidedDisplacement :
    (S : List CCM24VisiblePrime) → FiniteEulerTwoSidedRenewalIndex S → ℝ
  | [], _ => 0
  | p :: S, index =>
      primeTwoSidedDisplacement p index.1 +
        finiteEulerTwoSidedDisplacement S index.2

theorem finiteEulerTwoSidedNormalizedWeight_nonneg
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    0 ≤ finiteEulerTwoSidedNormalizedWeight S index := by
  induction S with
  | nil => simp [finiteEulerTwoSidedNormalizedWeight]
  | cons p S ih =>
      exact mul_nonneg (primeTwoSidedNormalizedWeight_nonneg p index.1)
        (ih index.2)

theorem finiteEulerTwoSidedDisplacement_nonneg
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    0 ≤ finiteEulerTwoSidedDisplacement S index := by
  induction S with
  | nil => simp [finiteEulerTwoSidedDisplacement]
  | cons p S ih =>
      exact add_nonneg (primeTwoSidedDisplacement_nonneg p index.1)
        (ih index.2)

/-- Exact total variation of the normalized two-sided law. -/
theorem finiteEulerTwoSidedNormalizedWeight_hasSum
    (S : List CCM24VisiblePrime) :
    HasSum (finiteEulerTwoSidedNormalizedWeight S)
      ((S.map fun p => 1 - ccm24PrimeEulerCoefficient p ^ 2).prod) := by
  induction S with
  | nil =>
      simp [finiteEulerTwoSidedNormalizedWeight]
  | cons p S ih =>
      have hp : HasSum (primeTwoSidedNormalizedWeight p)
          (1 - ccm24PrimeEulerCoefficient p ^ 2) := by
        simpa [tsum_primeTwoSidedNormalizedWeight p] using
          (summable_primeTwoSidedNormalizedWeight p).hasSum
      have hprod : Summable (fun index :
          PrimeTwoSidedRenewalIndex × FiniteEulerTwoSidedRenewalIndex S =>
            primeTwoSidedNormalizedWeight p index.1 *
              finiteEulerTwoSidedNormalizedWeight S index.2) := by
        rw [summable_prod_of_nonneg]
        · constructor
          · intro index
            exact ih.summable.mul_left
              (primeTwoSidedNormalizedWeight p index)
          · exact ((summable_primeTwoSidedNormalizedWeight p).mul_right
                ((S.map fun q =>
                  1 - ccm24PrimeEulerCoefficient q ^ 2).prod)).congr
              (fun index => by
                have h := ih.summable.tsum_mul_left
                  (primeTwoSidedNormalizedWeight p index)
                rw [ih.tsum_eq] at h
                simpa using h.symm)
        · intro index
          exact mul_nonneg
            (primeTwoSidedNormalizedWeight_nonneg p index.1)
            (finiteEulerTwoSidedNormalizedWeight_nonneg S index.2)
      simpa [finiteEulerTwoSidedNormalizedWeight] using hp.mul ih hprod

theorem summable_finiteEulerTwoSidedNormalizedWeight
    (S : List CCM24VisiblePrime) :
    Summable (finiteEulerTwoSidedNormalizedWeight S) :=
  (finiteEulerTwoSidedNormalizedWeight_hasSum S).summable

/-- The complete normalized two-sided total variation is at most one. -/
theorem tsum_finiteEulerTwoSidedNormalizedWeight_le_one
    (S : List CCM24VisiblePrime) :
    ∑' index : FiniteEulerTwoSidedRenewalIndex S,
      finiteEulerTwoSidedNormalizedWeight S index ≤ 1 := by
  rw [(finiteEulerTwoSidedNormalizedWeight_hasSum S).tsum_eq]
  induction S with
  | nil => simp
  | cons p S ih =>
      simp only [List.map_cons, List.prod_cons]
      have hp : 0 ≤ 1 - ccm24PrimeEulerCoefficient p ^ 2 := by
        nlinarith [sq_nonneg (ccm24PrimeEulerCoefficient p),
          ccm24PrimeEulerCoefficient_nonneg p,
          ccm24PrimeEulerCoefficient_lt_one p]
      have hple : 1 - ccm24PrimeEulerCoefficient p ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (ccm24PrimeEulerCoefficient p)]
      have hprodnonneg : 0 ≤
          (S.map fun q => 1 - ccm24PrimeEulerCoefficient q ^ 2).prod := by
        apply List.prod_nonneg
        intro x hx
        rcases List.mem_map.mp hx with ⟨q, _hq, rfl⟩
        nlinarith [sq_nonneg (ccm24PrimeEulerCoefficient q),
          ccm24PrimeEulerCoefficient_nonneg q,
          ccm24PrimeEulerCoefficient_lt_one q]
      calc
        _ ≤ 1 * (S.map fun q =>
              1 - ccm24PrimeEulerCoefficient q ^ 2).prod := by
          exact mul_le_mul_of_nonneg_right hple hprodnonneg
        _ ≤ 1 := by simpa using ih

end CCM24FiniteSTwoSidedRenewal
end CCM25Concrete
end Source
end ConnesWeilRH
