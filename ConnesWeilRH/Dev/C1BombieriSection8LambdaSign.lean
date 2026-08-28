/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8EndpointWirtinger

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, twentieth slice: reciprocal eigenvalue sign

For a nonzero weighted eigenvector, this leaf combines the finite (8.11)
identity and its Wirtinger remainder with the explicit reciprocal relation
`lambda * Lambda = 1`.  It proves positivity of the real eigenvalue
`lambda`, while keeping its reality, reciprocal relation, and nonzero-vector
hypotheses as caller-owned data.

DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8LambdaSign

open ConnesWeilRH.Source.C1BombieriSection7Gamma
open ConnesWeilRH.Source.C1BombieriSection8EigenGram
open ConnesWeilRH.Source.C1BombieriSection8EndpointWirtinger
open ConnesWeilRH.Source.C1BombieriSection8TotalAssembly
open scoped ComplexConjugate

variable {n : Nat}

/-- The real squared mass of the weighted coordinate vector in (7.2). -/
noncomputable def bombieriWMass (gamma : Fin n -> Real)
    (z : Fin n -> Complex) : Real :=
  ∑ i, Complex.normSq (bombieriWOfZ gamma z i)

/-- The complex Gram mass in the eigen-relation is the real cast of
`bombieriWMass`. -/
theorem ofReal_bombieriWMass (gamma : Fin n -> Real) (z : Fin n -> Complex) :
    Complex.ofReal (bombieriWMass gamma z)
      = ∑ i, bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i) := by
  unfold bombieriWMass
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Complex.mul_conj _).symm

/-- The weighted mass is strictly positive when the original coordinate
vector is nonzero; every `(1/4 + gamma_i^2)` weight is strictly positive. -/
theorem bombieriWMass_pos_of_ne_zero (gamma : Fin n -> Real)
    (z : Fin n -> Complex) (hz : z ≠ 0) :
    0 < bombieriWMass gamma z := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    funext j
    exact h j
  have hweight : ((1 / 4 + gamma i ^ 2 : Real) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hw : bombieriWOfZ gamma z i ≠ 0 := by
    unfold bombieriWOfZ
    exact mul_ne_zero hweight hi
  have hterm : 0 < Complex.normSq (bombieriWOfZ gamma z i) :=
    Complex.normSq_pos.mpr hw
  unfold bombieriWMass
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i))

/-- Multiplying the weighted eigen-relation by the explicit reciprocal
eigenvalue gives the exact (8.11) identity without division. -/
theorem lambda_mass_eq_KstarGram (t : Real) (gamma : Fin n -> Real)
    (z : Fin n -> Complex) (Lam : Complex)
    (lam : Real)
    (h : bombieriWOfZ gamma z
        = Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z))
    (hrecip : (lam : Complex) * Lam = 1) :
    (lam : Complex) * Complex.ofReal (bombieriWMass gamma z)
      = bombieriKstarGram t gamma z := by
  have heigen : (∑ i, bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i))
      = Lam * bombieriKstarGram t gamma z := by
    simpa only [bombieriKstarGram] using bombieriEigen_gram t gamma z Lam h
  calc
    (lam : Complex) * Complex.ofReal (bombieriWMass gamma z)
      = (lam : Complex)
          * (∑ i, bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i)) := by
            rw [ofReal_bombieriWMass]
    _ = (lam : Complex) * (Lam * bombieriKstarGram t gamma z) := by
          rw [heigen]
    _ = ((lam : Complex) * Lam) * bombieriKstarGram t gamma z := by ring
    _ = bombieriKstarGram t gamma z := by rw [hrecip, one_mul]

/-- The reciprocal eigenvalue times the positive weighted mass is the real
nonnegative Wirtinger remainder. -/
theorem lambda_mass_eq_nonneg (t : Real) (ht : 0 < t)
    (gamma : Fin n -> Real) (z : Fin n -> Complex) (Lam : Complex)
    (lam : Real)
    (h : bombieriWOfZ gamma z
        = Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z))
    (hrecip : (lam : Complex) * Lam = 1) :
    ∃ S : Real, 0 ≤ S ∧ lam * bombieriWMass gamma z = S := by
  obtain ⟨S, hS, hgram⟩ := bombieriKstarGram_eq_ofReal_nonneg t ht gamma z
  refine ⟨S, hS, ?_⟩
  have hcomplex := lambda_mass_eq_KstarGram t gamma z Lam lam h hrecip
  rw [hgram] at hcomplex
  simpa using congrArg Complex.re hcomplex

/-- A real reciprocal eigenvalue is nonnegative on every nonzero weighted
eigenvector. -/
theorem lambda_nonneg_of_eigen (t : Real) (ht : 0 < t)
    (gamma : Fin n -> Real) (z : Fin n -> Complex) (Lam : Complex)
    (lam : Real) (hz : z ≠ 0)
    (h : bombieriWOfZ gamma z
        = Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z))
    (hrecip : (lam : Complex) * Lam = 1) :
    0 ≤ lam := by
  obtain ⟨S, hS, hmass⟩ := lambda_mass_eq_nonneg t ht gamma z Lam lam h hrecip
  have hpositive := bombieriWMass_pos_of_ne_zero gamma z hz
  by_contra hneg
  have hlam : lam < 0 := lt_of_not_ge hneg
  have hproduct : lam * bombieriWMass gamma z < 0 :=
    mul_neg_of_neg_of_pos hlam hpositive
  rw [hmass] at hproduct
  exact (not_lt_of_ge hS) hproduct

/-- In the reciprocal branch the same real eigenvalue is strictly positive.
The zero eigenvalue branch is already nonnegative and is handled separately
by the sign-count consumer. -/
theorem lambda_pos_of_eigen (t : Real) (ht : 0 < t)
    (gamma : Fin n -> Real) (z : Fin n -> Complex) (Lam : Complex)
    (lam : Real) (hz : z ≠ 0)
    (h : bombieriWOfZ gamma z
        = Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z))
    (hrecip : (lam : Complex) * Lam = 1) :
    0 < lam := by
  have hnonneg := lambda_nonneg_of_eigen t ht gamma z Lam lam hz h hrecip
  have hne : lam ≠ 0 := by
    intro hzero
    have hbad := hrecip
    rw [hzero] at hbad
    norm_num at hbad
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end C1BombieriSection8LambdaSign
end Source
end ConnesWeilRH
