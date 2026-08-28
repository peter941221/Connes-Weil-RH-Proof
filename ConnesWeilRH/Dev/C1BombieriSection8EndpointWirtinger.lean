/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8Boundary
import ConnesWeilRH.Dev.C1BombieriSection8TotalAssembly
import ConnesWeilRH.Dev.C1BombieriSection8WirtingerFull

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, nineteenth slice: endpoint correction meets (8.13)

This leaf identifies the endpoint correction from the finite (8.11) sum
with the even/odd endpoint part of the Wirtinger identity (8.13).  Their
difference is therefore exactly the nonnegative remainder supplied by
`wirtingerFull`.

DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8EndpointWirtinger

open ConnesWeilRH.Source.C1BombieriSection8Boundary
open ConnesWeilRH.Source.C1BombieriSection8EndpointCorrection
open ConnesWeilRH.Source.C1BombieriSection8ExpMass
open ConnesWeilRH.Source.C1BombieriSection8QForm
open ConnesWeilRH.Source.C1BombieriSection8TotalAssembly
open ConnesWeilRH.Source.C1BombieriSection8WirtingerFull
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice3
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice5
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice7
open scoped ComplexConjugate
open MeasureTheory

variable {n : Nat}

/-- The endpoint correction in a form matching the left side of
`bombieriEvenOddBoundary`. -/
theorem endpointCorrection_raw (t : Real) (gamma : Fin n -> Real)
    (z : Fin n -> Complex) :
    endpointCorrection t gamma z
      = ((Real.exp t + Real.exp (-t) : Real) : Complex)
          / ((2 * (Real.exp t - Real.exp (-t) : Real) : Complex))
          * (expSum gamma z t * conj (expSum gamma z t)
            + expSum gamma z (-t) * conj (expSum gamma z (-t)))
        - (expSum gamma z t * conj (expSum gamma z (-t))
            + conj (expSum gamma z t) * expSum gamma z (-t))
          / ((Real.exp t - Real.exp (-t) : Real) : Complex) := by
  have htwo (r : Real) : Complex.ofReal (2 * r)
      = (2 : Complex) * Complex.ofReal r := by
    apply Complex.ext <;> simp
  unfold endpointCorrection
  simp only [Complex.ofReal_div]
  rw [htwo]
  norm_num; ring

/-- A conjugate square divided by four is the squared norm of its half. -/
private theorem half_square (a : Complex) :
    a * conj a / 4 = Complex.ofReal (Complex.normSq (a / 2)) := by
  calc
    a * conj a / 4 = Complex.ofReal (Complex.normSq a) / 4 := by
      rw [Complex.mul_conj]
    _ = Complex.ofReal (Complex.normSq a / 4) :=
      (Complex.ofReal_div (Complex.normSq a) 4).symm
    _ = Complex.ofReal (Complex.normSq (a / 2)) := by
      congr 1
      rw [Complex.normSq_div]
      norm_num

/-- The even Wirtinger endpoint weight in the exponential ratio used by
the boundary recombination. -/
private theorem tanhHalf_eq_expRatio (t : Real) :
    Real.tanh (t / 2) = (Real.exp t - 1) / (Real.exp t + 1) := by
  calc
    Real.tanh (t / 2)
        = (Real.exp t - Real.exp (-t))
            / ((Real.exp (t / 2) + Real.exp (-t / 2)) ^ 2) :=
          (tanhHalf_eq_ratio t).symm
    _ = (Real.exp t - 1) / (Real.exp t + 1) := by
      have hhalf : Real.exp (-t / 2) = (Real.exp (t / 2))⁻¹ := by
        rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg]
      have hwhole : Real.exp (-t) = (Real.exp t)⁻¹ := by
        rw [Real.exp_neg]
      have hpow : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
        rw [← Real.exp_add (t / 2) (t / 2)]
        congr 1
        ring
      have hne : Real.exp (t / 2) ≠ 0 := Real.exp_ne_zero _
      have hsum : Real.exp (t / 2) + (Real.exp (t / 2))⁻¹ ≠ 0 :=
        ne_of_gt (add_pos (Real.exp_pos _) (inv_pos.mpr (Real.exp_pos _)))
      have hden : Real.exp (t / 2) * Real.exp (t / 2) + 1 ≠ 0 :=
        ne_of_gt (by positivity)
      rw [hhalf, hwhole, hpow]
      field_simp [hne, hsum, hden]
      ring

/-- The odd Wirtinger endpoint weight in the exponential ratio used by
the boundary recombination. -/
private theorem cothHalf_eq_expRatio (t : Real) (ht : 0 < t) :
    Real.cosh (t / 2) / Real.sinh (t / 2)
      = (Real.exp t + 1) / (Real.exp t - 1) := by
  calc
    Real.cosh (t / 2) / Real.sinh (t / 2)
        = (Real.exp t - Real.exp (-t))
            / ((Real.exp (t / 2) - Real.exp (-t / 2)) ^ 2) :=
          (coshHalf_div_sinhHalf_eq_ratio t ht).symm
    _ = (Real.exp t + 1) / (Real.exp t - 1) := by
      have hhalf : Real.exp (-t / 2) = (Real.exp (t / 2))⁻¹ := by
        rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg]
      have hwhole : Real.exp (-t) = (Real.exp t)⁻¹ := by
        rw [Real.exp_neg]
      have hpow : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
        rw [← Real.exp_add (t / 2) (t / 2)]
        congr 1
        ring
      have hne : Real.exp (t / 2) ≠ 0 := Real.exp_ne_zero _
      have hwholePos : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
      have hden : Real.exp (t / 2) * Real.exp (t / 2) - 1 ≠ 0 := by
        rw [← hpow]
        exact ne_of_gt (sub_pos.mpr hwholePos)
      have hdiffForm : Real.exp (t / 2) - (Real.exp (t / 2))⁻¹
          = (Real.exp (t / 2) * Real.exp (t / 2) - 1) / Real.exp (t / 2) := by
        field_simp [hne]
      have hnumForm : Real.exp (t / 2) * Real.exp (t / 2)
          - (Real.exp (t / 2) * Real.exp (t / 2))⁻¹
          = ((Real.exp (t / 2) * Real.exp (t / 2) - 1)
              * (Real.exp (t / 2) * Real.exp (t / 2) + 1))
              / (Real.exp (t / 2) * Real.exp (t / 2)) := by
        field_simp [hne]; ring
      rw [hhalf, hwhole, hpow]
      rw [hnumForm, hdiffForm]
      field_simp [hne, hden]

/-- The raw two-endpoint correction is exactly the pair of endpoint weights
appearing in `wirtingerFull_weights`. -/
private theorem rawBoundary_eq_wirtingerBoundary (a b : Complex)
    (t : Real) (ht : 0 < t) :
    ((Real.exp t + Real.exp (-t) : Real) : Complex)
        / ((2 * (Real.exp t - Real.exp (-t) : Real) : Complex))
        * (a * conj a + b * conj b)
      - (a * conj b + conj a * b)
        / ((Real.exp t - Real.exp (-t) : Real) : Complex)
      = Complex.ofReal
          (Real.tanh (t / 2) * Complex.normSq ((a + b) / 2)
            + (Real.cosh (t / 2) / Real.sinh (t / 2))
              * Complex.normSq ((a - b) / 2)) := by
  calc
    ((Real.exp t + Real.exp (-t) : Real) : Complex)
        / ((2 * (Real.exp t - Real.exp (-t) : Real) : Complex))
        * (a * conj a + b * conj b)
      - (a * conj b + conj a * b)
        / ((Real.exp t - Real.exp (-t) : Real) : Complex)
      = ((Real.exp t - 1 : Real) : Complex)
          / ((Real.exp t + 1 : Real) : Complex)
          * ((a + b) * conj (a + b) / 4)
        + ((Real.exp t + 1 : Real) : Complex)
          / ((Real.exp t - 1 : Real) : Complex)
          * ((a - b) * conj (a - b) / 4) := by
            exact bombieriEvenOddBoundary a b t (ne_of_gt ht)
    _ = Complex.ofReal
          (Real.tanh (t / 2) * Complex.normSq ((a + b) / 2)
            + (Real.cosh (t / 2) / Real.sinh (t / 2))
              * Complex.normSq ((a - b) / 2)) := by
            rw [half_square (a + b), half_square (a - b),
              ← Complex.ofReal_div, ← Complex.ofReal_div,
              ← Complex.ofReal_mul, ← Complex.ofReal_mul,
              ← Complex.ofReal_add, ← tanhHalf_eq_expRatio,
              ← cothHalf_eq_expRatio t ht]

/-- The endpoint correction from (8.11) equals the endpoint part in the
full Wirtinger identity (8.13). -/
theorem endpointCorrection_eq_wirtingerBoundary (t : Real) (ht : 0 < t)
    (gamma : Fin n -> Real) (z : Fin n -> Complex) :
    endpointCorrection t gamma z
      = Complex.ofReal
          (Real.tanh (t / 2)
              * Complex.normSq ((expSum gamma z t + expSum gamma z (-t)) / 2)
            + (Real.cosh (t / 2) / Real.sinh (t / 2))
              * Complex.normSq ((expSum gamma z t - expSum gamma z (-t)) / 2)) := by
  calc
    endpointCorrection t gamma z
      = ((Real.exp t + Real.exp (-t) : Real) : Complex)
          / ((2 * (Real.exp t - Real.exp (-t) : Real) : Complex))
          * (expSum gamma z t * conj (expSum gamma z t)
            + expSum gamma z (-t) * conj (expSum gamma z (-t)))
        - (expSum gamma z t * conj (expSum gamma z (-t))
            + conj (expSum gamma z t) * expSum gamma z (-t))
          / ((Real.exp t - Real.exp (-t) : Real) : Complex) :=
            endpointCorrection_raw t gamma z
    _ = Complex.ofReal
          (Real.tanh (t / 2)
              * Complex.normSq ((expSum gamma z t + expSum gamma z (-t)) / 2)
            + (Real.cosh (t / 2) / Real.sinh (t / 2))
              * Complex.normSq ((expSum gamma z t - expSum gamma z (-t)) / 2)) :=
            rawBoundary_eq_wirtingerBoundary (expSum gamma z t)
              (expSum gamma z (-t)) t ht

/-- The (8.11) right side is a real nonnegative Wirtinger remainder. -/
theorem qIntegrand_sub_endpointCorrection_eq_nonneg (t : Real) (ht : 0 < t)
    (gamma : Fin n -> Real) (z : Fin n -> Complex) :
    ∃ S : Real, 0 ≤ S ∧
      (∫ x in -t..t,
          qIntegrand (expSum gamma z) (expSum gamma (dcoef gamma z)) x)
        - endpointCorrection t gamma z = Complex.ofReal S := by
  obtain ⟨S, hS, hQ⟩ := wirtingerFull_weights t ht
    (expSum gamma z) (expSum gamma (dcoef gamma z))
    (fun x => by simpa only [dcoef] using hasDerivAt_expSum gamma z x)
    (continuous_expSum gamma (dcoef gamma z))
  refine ⟨S, hS, ?_⟩
  rw [hQ, endpointCorrection_eq_wirtingerBoundary t ht gamma z,
    ← Complex.ofReal_sub]
  congr 1
  ring

/-- The finite weighted `K*` Gram sum is a nonnegative real cast. -/
theorem bombieriKstarGram_eq_ofReal_nonneg (t : Real) (ht : 0 < t)
    (gamma : Fin n -> Real) (z : Fin n -> Complex) :
    ∃ S : Real, 0 ≤ S ∧ bombieriKstarGram t gamma z = Complex.ofReal S := by
  obtain ⟨S, hS, hQ⟩ := qIntegrand_sub_endpointCorrection_eq_nonneg t ht gamma z
  refine ⟨S, hS, ?_⟩
  calc
    bombieriKstarGram t gamma z
      = (∫ x in -t..t,
          qIntegrand (expSum gamma z) (expSum gamma (dcoef gamma z)) x)
        - endpointCorrection t gamma z :=
          bombieriKstarGram_eq_qIntegrand_sub_endpointCorrection t ht gamma z
    _ = Complex.ofReal S := hQ

end C1BombieriSection8EndpointWirtinger
end Source
end ConnesWeilRH
