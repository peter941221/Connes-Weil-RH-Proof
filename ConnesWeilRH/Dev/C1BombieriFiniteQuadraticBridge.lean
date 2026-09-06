/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8EndpointWirtinger

/-!
# Finite Bombieri quadratic-form bridge

The section-7 ownership identity identifies the finite Hermitian matrix
quadratic form on the weighted vector `w = (1/4 + γ^2) z` with the weighted
`K*` Gram sum.  The section-8 Wirtinger chain already proves that Gram sum is
a nonnegative real cast for `t > 0`.  This leaf exposes that implication as a
consumer of the finite matrix owner.

This is still a finite-certificate statement.  It does not identify the
quadratic form with the whole `qw` on the healthy `CompactLog` owner.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriFiniteQuadraticBridge

open ConnesWeilRH.Source.C1BombieriSection7Gamma
open ConnesWeilRH.Source.C1BombieriSection7H
open ConnesWeilRH.Source.C1BombieriSection7Readback
open ConnesWeilRH.Source.C1BombieriSection8EigenGram
open ConnesWeilRH.Source.C1BombieriSection8EndpointWirtinger
open ConnesWeilRH.Source.C1BombieriSection8TotalAssembly
open scoped ComplexConjugate

variable {n : Nat}

/-- The weighted finite `H` quadratic form is exactly Bombieri's weighted
`K*` Gram sum, with no eigenvector or distinctness assumption. -/
theorem bombieriHMatrix_quadraticForm_eq_KstarGram (t : Real)
    (gamma : Fin n → Real) (z : Fin n → Complex) :
    star (bombieriWOfZ gamma z) ⬝ᵥ
        (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)
      = bombieriKstarGram t gamma z := by
  unfold dotProduct bombieriKstarGram
  simp only [Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hconj : star (bombieriWOfZ gamma z i) =
      ((1 / 4 + gamma i ^ 2 : Real) : Complex) * star (z i) := by
    simpa only [starRingEnd_apply] using conj_bombieriWOfZ gamma z i
  change star (bombieriWOfZ gamma z i) *
      (fun j => bombieriHMatrix gamma t i j) ⬝ᵥ bombieriWOfZ gamma z = _
  rw [hconj]
  simp only [dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [bombieriHMatrix, Matrix.of_apply, bombieriWOfZ]
  calc
    ((1 / 4 + gamma i ^ 2 : Real) : Complex) * star (z i) *
          (bombieriH (gamma i) (gamma j) t
            * (((1 / 4 + gamma j ^ 2 : Real) : Complex) * z j))
        = (((1 / 4 + gamma i ^ 2 : Real) : Complex) * star (z i)) *
            (bombieriH (gamma i) (gamma j) t
              * ((1 / 4 + gamma j ^ 2 : Real) : Complex)) * z j := by ring
    _ = (((1 / 4 + gamma i ^ 2 : Real) : Complex) * star (z i)) *
          (((2 * t : Real) : Complex) * bombieriKstar (gamma i) (gamma j) t) * z j := by
      rw [mul_comm (bombieriH (gamma i) (gamma j) t)
        ((1 / 4 + gamma j ^ 2 : Real) : Complex),
        bombieriH_mul_weight_eq]
    _ = _ := by
      simp only [starRingEnd_apply]
      ring

/-- The finite weighted `H` quadratic form is a nonnegative real cast for
positive `t`.  This is a genuine finite positivity result, not a `qw` claim. -/
theorem bombieriHMatrix_quadraticForm_eq_ofReal_nonneg (t : Real) (ht : 0 < t)
    (gamma : Fin n → Real) (z : Fin n → Complex) :
    ∃ S : Real, 0 ≤ S ∧
      star (bombieriWOfZ gamma z) ⬝ᵥ
          (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)
        = Complex.ofReal S := by
  obtain ⟨S, hS, hGram⟩ := bombieriKstarGram_eq_ofReal_nonneg t ht gamma z
  refine ⟨S, hS, ?_⟩
  rw [bombieriHMatrix_quadraticForm_eq_KstarGram]
  exact hGram

end C1BombieriFiniteQuadraticBridge
end Source
end ConnesWeilRH
