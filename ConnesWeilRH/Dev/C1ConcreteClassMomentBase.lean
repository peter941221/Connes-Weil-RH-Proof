/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ScaledExpRationalEnvelope
import ConnesWeilRH.Dev.C1RationalPowerIntegral
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Record 1139/1145: concrete class-moment certificate (computable data)

The computable rational data of the 1139 concrete class-moment
certificate: Taylor coefficients, the cached 666-entry convolution, the
endpoint/moment recursions, and the comparison constants.  Moved
verbatim from C1ConcreteClassMomentCertificate in the record-1145 RED-8
module split; the namespace is intentionally kept so every
fully-qualified name is unchanged.  The numeric gate itself lives in
C1ConcreteClassMomentCertificate and its kernel-checked grounding
machinery in C1ConcreteClassMomentGrounding{A,B,C}.

RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ConcreteClassMomentCertificate

open MeasureTheory Set
open Polynomial
open scoped BigOperators Interval

-- The computable rational data of the 1139 concrete class-moment
-- certificate: Taylor coefficients, the cached convolution, the
-- endpoint/moment recursions, and the comparison constants.  Moved
-- verbatim from C1ConcreteClassMomentCertificate (record 1145 RED-8
-- module split); the namespace is intentionally kept so every
-- fully-qualified name is unchanged.


/-! ## Exact rational data used for the finite certificate -/

section Computable

def rationalRadiusQ : ℚ := 97 / 100

noncomputable def taylorScaledPolynomialQ : ℚ[X] :=
  ∑ j ∈ Finset.range 20,
    Polynomial.C (((-(2 / 35 : ℚ)) ^ j) / (j.factorial : ℚ)) *
      Polynomial.X ^ j

noncomputable def rationalPowerPolynomialQ : ℚ[X] :=
  taylorScaledPolynomialQ ^ 35

def taylorCoefficientQ (k : ℕ) : ℚ :=
  if k < 20 then
    ((-(2 / 35 : ℚ)) ^ k) / (k.factorial : ℚ)
  else 0

/-- Computable coefficient convolution used by the exact rational audit. -/
def listCoeffQ (xs : List ℚ) (k : ℕ) : ℚ :=
  List.getD xs k 0

def zeroPowerCoefficientListQ : List ℚ :=
  (List.range 666).map fun k => if k = 0 then 1 else 0

/-- A cached coefficient table: each power layer is computed once before the
next layer is formed.  This keeps the exact rational decision procedure
finite and independent of Polynomial's noncomputable ring implementation. -/
def powerCoefficientListQ : ℕ → List ℚ
  | 0 => zeroPowerCoefficientListQ
  | n + 1 =>
      let prev := powerCoefficientListQ n
      (List.range 666).map fun k =>
        ∑ i ∈ Finset.range 20,
          if i ≤ k then
            listCoeffQ prev (k - i) * taylorCoefficientQ i
          else 0

def powerCoefficientQ (n k : ℕ) : ℚ :=
  listCoeffQ (powerCoefficientListQ n) k

def powerCoefficientQSlow : ℕ → ℕ → ℚ
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => fun k =>
      ∑ x ∈ Finset.antidiagonal k,
        powerCoefficientQSlow n x.1 * taylorCoefficientQ x.2

def rationalPowerCoefficientQ (k : ℕ) : ℚ :=
  powerCoefficientQSlow 35 k

private def rationalPowerCoefficientQFast (k : ℕ) : ℚ :=
  powerCoefficientQ 35 k

theorem listCoeff_range_map (f : ℕ → ℚ) (k : ℕ) (hk : k < 666) :
    listCoeffQ ((List.range 666).map f) k = f k := by
  unfold listCoeffQ
  rw [List.getD_eq_getElem _ _]
  · rw [List.getElem_map]
    simp
  · simp [hk]

theorem powerCoefficientQ_succ (n k : ℕ) (hk : k < 666) :
    powerCoefficientQ (n + 1) k =
      ∑ i ∈ Finset.range 20,
        if i ≤ k then powerCoefficientQ n (k - i) * taylorCoefficientQ i else 0 := by
  change listCoeffQ (powerCoefficientListQ (n + 1)) k = _
  rw [powerCoefficientListQ]
  exact listCoeff_range_map _ k hk

private theorem powerCoefficientQSlow_succ (n k : ℕ) :
    powerCoefficientQSlow (n + 1) k =
      ∑ i ∈ Finset.range (k + 1),
        powerCoefficientQSlow n (k - i) * taylorCoefficientQ i := by
  change (∑ x ∈ Finset.antidiagonal k,
      powerCoefficientQSlow n x.1 * taylorCoefficientQ x.2) = _
  rw [Finset.Nat.antidiagonal_eq_map']
  simp

private theorem sum_range_eq_trunc (f : ℕ → ℚ) (hf : ∀ i, 20 ≤ i → f i = 0) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), f i) =
      ∑ i ∈ Finset.range 20, if i ≤ k then f i else 0 := by
  classical
  by_cases hk : k < 20
  · have hsub : Finset.range (k + 1) ⊆ Finset.range 20 := by
      intro i hi
      have hik : i < k + 1 := Finset.mem_range.mp hi
      have hkk : k + 1 ≤ 20 := by omega
      exact Finset.mem_range.mpr (lt_of_lt_of_le hik hkk)
    calc
      (∑ i ∈ Finset.range (k + 1), f i) =
          ∑ i ∈ Finset.range (k + 1), if i ≤ k then f i else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [Nat.le_of_lt_succ (Finset.mem_range.mp hi)]
      _ = ∑ i ∈ Finset.range 20, if i ≤ k then f i else 0 := by
        have hzero : ∀ i ∈ Finset.range 20, i ∉ Finset.range (k + 1) →
            (if i ≤ k then f i else 0) = 0 := by
          intro i hi hnot
          have hik : k + 1 ≤ i := Nat.le_of_not_gt (Finset.mem_range.not.mp hnot)
          simp [show ¬ i ≤ k by omega]
        exact Finset.sum_subset hsub hzero
  · have h20k : 20 ≤ k := Nat.le_of_not_gt hk
    have hsub : Finset.range 20 ⊆ Finset.range (k + 1) := by
      intro i hi
      have hi20 : i < 20 := Finset.mem_range.mp hi
      exact Finset.mem_range.mpr (by omega)
    calc
      (∑ i ∈ Finset.range (k + 1), f i) =
          ∑ i ∈ Finset.range (k + 1), if i < 20 then f i else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hi20 : i < 20
            · simp [hi20]
            · rw [if_neg hi20, hf i (Nat.le_of_not_gt hi20)]
      _ = ∑ i ∈ Finset.range 20, if i ≤ k then f i else 0 := by
        have hsum :
            (∑ i ∈ Finset.range 20, if i < 20 then f i else 0) =
              ∑ i ∈ Finset.range (k + 1), if i < 20 then f i else 0 := by
          apply Finset.sum_subset hsub
          intro i hi hnot
          have hi20 : ¬ i < 20 := Finset.mem_range.not.mp hnot
          simp [hi20]
        rw [← hsum]
        apply Finset.sum_congr rfl
        intro i hi
        have hi20 : i < 20 := Finset.mem_range.mp hi
        have hik : i ≤ k := by omega
        simp [hi20, hik]

private theorem powerCoefficientQ_eq_slow : ∀ n k, k < 666 →
    powerCoefficientQ n k = powerCoefficientQSlow n k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      change listCoeffQ zeroPowerCoefficientListQ k = _
      rw [show zeroPowerCoefficientListQ =
        (List.range 666).map (fun j => if j = 0 then 1 else 0) by rfl]
      rw [listCoeff_range_map _ k hk]
      rfl
  | succ n ih =>
      intro k hk
      rw [powerCoefficientQ_succ n k hk, powerCoefficientQSlow_succ]
      have hzero : ∀ i, 20 ≤ i →
          powerCoefficientQSlow n (k - i) * taylorCoefficientQ i = 0 := by
        intro i hi
        simp [taylorCoefficientQ, Nat.not_lt.mpr hi]
      rw [sum_range_eq_trunc
        (fun i => powerCoefficientQSlow n (k - i) * taylorCoefficientQ i)
        hzero k]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hik : i ≤ k
      · rw [if_pos hik, if_pos hik,
          ih (k - i) (lt_of_le_of_lt (Nat.sub_le k i) hk)]
      · simp [hik]

private theorem rationalPowerCoefficientQFast_eq_slow (k : ℕ) (hk : k < 666) :
    rationalPowerCoefficientQFast k = rationalPowerCoefficientQ k := by
  exact powerCoefficientQ_eq_slow 35 k hk

theorem powerCoefficientQ_eq_slow_public (n k : ℕ) (hk : k < 666) :
    powerCoefficientQ n k = powerCoefficientQSlow n k := by
  exact powerCoefficientQ_eq_slow n k hk

theorem taylorScaledPolynomialQ_coeff (k : ℕ) :
    taylorScaledPolynomialQ.coeff k = taylorCoefficientQ k := by
  classical
  unfold taylorScaledPolynomialQ taylorCoefficientQ
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k < 20
  · rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j hj hjk
      simp [hjk.symm]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hk)).elim
  · simp only [if_neg hk]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : k ≠ j := by
      exact ne_of_gt (lt_of_lt_of_le (Finset.mem_range.mp hj)
        (Nat.le_of_not_gt hk))
    simp [hjk]

theorem powerCoefficientQSlow_eq_polynomial_coeff (n k : ℕ) :
    powerCoefficientQSlow n k =
      (taylorScaledPolynomialQ ^ n).coeff k := by
  induction n generalizing k with
  | zero =>
      simp [powerCoefficientQSlow, Polynomial.coeff_one]
  | succ n ih =>
      rw [powerCoefficientQSlow, pow_succ, coeff_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih x.1, taylorScaledPolynomialQ_coeff]

def endpointAQ : ℕ → ℚ
  | 0 => 2 * rationalRadiusQ
  | 1 => 0
  | k + 2 =>
      rationalRadiusQ /
          (((k : ℚ) + 1) * (1 - rationalRadiusQ ^ 2) ^ (k + 1)) +
        ((2 * (k : ℚ) + 1) / (2 * ((k : ℚ) + 1))) * endpointAQ (k + 1)

def endpointBQ : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | k + 2 =>
      ((2 * (k : ℚ) + 1) / (2 * ((k : ℚ) + 1))) * endpointBQ (k + 1)

def momentAQ : ℕ → ℚ
  | 0 => 2 * rationalRadiusQ ^ 3 / 3
  | k + 1 => endpointAQ (k + 1) - endpointAQ k

def momentBQ : ℕ → ℚ
  | 0 => 0
  | k + 1 => endpointBQ (k + 1) - endpointBQ k

structure ComparisonDataQ where
  a0 : ℚ
  b0 : ℚ
  a2 : ℚ
  b2 : ℚ

/-- The four exact comparison sums share one cached coefficient table. -/
def comparisonDataQ : ComparisonDataQ :=
  let coeffs := powerCoefficientListQ 35
  { a0 := ∑ k ∈ Finset.range 666, listCoeffQ coeffs k * endpointAQ k
    b0 := ∑ k ∈ Finset.range 666, listCoeffQ coeffs k * endpointBQ k
    a2 := ∑ k ∈ Finset.range 666, listCoeffQ coeffs k * momentAQ k
    b2 := ∑ k ∈ Finset.range 666, listCoeffQ coeffs k * momentBQ k }

def comparisonIntegral0AQ : ℚ := comparisonDataQ.a0

def comparisonIntegral0BQ : ℚ := comparisonDataQ.b0

def comparisonIntegral2AQ : ℚ := comparisonDataQ.a2

def comparisonIntegral2BQ : ℚ := comparisonDataQ.b2

def logLowerQ : ℚ := 41845914400698788 / 10 ^ 16

def logUpperQ : ℚ := 41845914400698789 / 10 ^ 16

def centralErrorQ : ℚ :=
  2 * rationalRadiusQ *
    (70 * (21 / ((Nat.factorial 20 : ℚ) * 20)))

def tailBudgetQ : ℚ := 1 / 10 ^ 16

def q28Moment0LoQ : ℚ :=
  2397466416982805 / 18014398509481984 - 1 / 10 ^ 15

def q28Moment0HiQ : ℚ :=
  2397466416982805 / 18014398509481984 + 1 / 10 ^ 15

def q28Moment2LoQ : ℚ :=
  8817094793947821 / 576460752303423488 - 1 / 10 ^ 15

def q28Moment2HiQ : ℚ :=
  8817094793947821 / 576460752303423488 + 1 / 10 ^ 15

end Computable
end C1ConcreteClassMomentCertificate
end Source
end ConnesWeilRH
