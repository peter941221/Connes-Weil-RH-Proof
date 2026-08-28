/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8EndpointCorrection
import ConnesWeilRH.Dev.C1BombieriSection8EigenGram
import ConnesWeilRH.Dev.C1BombieriSection8QForm

import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, eighteenth slice: the total (8.11) finite-sum assembly

This leaf joins the two channels of the weighted Bombieri (7.1) kernel
entry.  The Q-form channel is the interval integral of the finite
exponential sum, and the elementary channel is its exact endpoint
correction.  Thus the finite `K*` Gram sum appearing in the (7.4)
eigen-relation has the (8.11) shape without excluding repeated ordinates.

DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8TotalAssembly

open ConnesWeilRH.Source.C1BombieriSection7Gamma
open ConnesWeilRH.Source.C1BombieriSection7Readback
open ConnesWeilRH.Source.C1BombieriSection8EigenGram
open ConnesWeilRH.Source.C1BombieriSection8EndpointCorrection
open ConnesWeilRH.Source.C1BombieriSection8ExpMass
open ConnesWeilRH.Source.C1BombieriSection8KernelWeights
open ConnesWeilRH.Source.C1BombieriSection8QForm
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice3
open scoped ComplexConjugate
open MeasureTheory

variable {n : Nat}

/-- The finite weighted `K*` Gram sum on the right side of the (7.4)
eigen-relation after the `w = (1/4 + gamma^2) z` coordinate change. -/
noncomputable def bombieriKstarGram (t : Real) (gamma : Fin n -> Real)
    (z : Fin n -> Complex) : Complex :=
  ∑ i, ∑ j, ((2 * t : Real) : Complex)
    * bombieriKstar (gamma i) (gamma j) t * z j
    * (((1 / 4 + gamma i ^ 2 : Real) : Complex) * conj (z i))

/-- Transposing a finite double sum. -/
private theorem double_sum_swap (F : Fin n -> Fin n -> Complex) :
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j, F j i := by
  calc
    (∑ i, ∑ j, F i j) = ∑ j, ∑ i, F i j := Finset.sum_comm
    _ = ∑ i, ∑ j, F j i := rfl

/-- The Q-form channel is invariant under the index transposition needed by
the eigen-relation Gram sum. -/
private theorem qChannel_swap (t : Real) (gamma : Fin n -> Real)
    (z : Fin n -> Complex) :
    (∑ i, ∑ j, Complex.ofReal (1 / 4 + gamma i * gamma j)
        * winInt t (gamma j - gamma i) * (z j * conj (z i)))
      = ∑ i, ∑ j, Complex.ofReal (1 / 4 + gamma i * gamma j)
          * (z i * conj (z j)) * winInt t (gamma j - gamma i) := by
  calc
    (∑ i, ∑ j, Complex.ofReal (1 / 4 + gamma i * gamma j)
        * winInt t (gamma j - gamma i) * (z j * conj (z i)))
      = ∑ i, ∑ j, Complex.ofReal (1 / 4 + gamma j * gamma i)
          * winInt t (gamma i - gamma j) * (z i * conj (z j)) := by
            exact double_sum_swap (fun i j =>
              Complex.ofReal (1 / 4 + gamma i * gamma j)
                * winInt t (gamma j - gamma i) * (z j * conj (z i)))
    _ = ∑ i, ∑ j, Complex.ofReal (1 / 4 + gamma i * gamma j)
          * (z i * conj (z j)) * winInt t (gamma j - gamma i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            have hcoef : (1 / 4 + gamma j * gamma i : Real)
                = 1 / 4 + gamma i * gamma j := by ring
            have hfreq : gamma i - gamma j = -(gamma j - gamma i) := by ring
            rw [hcoef, hfreq, winInt_neg]
            ring

/-- The elementary correction channel is likewise invariant under the
index transposition. -/
private theorem correctionChannel_swap (t : Real) (gamma : Fin n -> Real)
    (z : Fin n -> Complex) :
    (∑ i, ∑ j, Complex.ofReal
        ((Real.cosh t * Real.cos (t * (gamma i - gamma j))
          - Real.cos (t * (gamma i + gamma j))) / Real.sinh t)
        * (z j * conj (z i)))
      = kernelEndpointCorrection t gamma z := by
  calc
    (∑ i, ∑ j, Complex.ofReal
        ((Real.cosh t * Real.cos (t * (gamma i - gamma j))
          - Real.cos (t * (gamma i + gamma j))) / Real.sinh t)
        * (z j * conj (z i)))
      = ∑ i, ∑ j, Complex.ofReal
          ((Real.cosh t * Real.cos (t * (gamma j - gamma i))
            - Real.cos (t * (gamma j + gamma i))) / Real.sinh t)
          * (z i * conj (z j)) := by
            exact double_sum_swap (fun i j => Complex.ofReal
              ((Real.cosh t * Real.cos (t * (gamma i - gamma j))
                - Real.cos (t * (gamma i + gamma j))) / Real.sinh t)
              * (z j * conj (z i)))
    _ = kernelEndpointCorrection t gamma z := by
      unfold kernelEndpointCorrection
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      have hdiff : t * (gamma j - gamma i) = -(t * (gamma i - gamma j)) := by
        ring
      have hsum : t * (gamma j + gamma i) = t * (gamma i + gamma j) := by
        ring
      rw [hdiff, Real.cos_neg, hsum]

/-- One weighted (7.1) kernel entry in the orientation used by the
eigen-relation Gram transport. -/
private theorem weighted_entry (t : Real) (ht : 0 < t)
    (x y : Real) (zx zy : Complex) :
    ((2 * t : Real) : Complex) * bombieriKstar x y t * zy
        * (((1 / 4 + x ^ 2 : Real) : Complex) * conj zx)
      = Complex.ofReal (1 / 4 + x * y) * winInt t (y - x)
          * (zy * conj zx)
        - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
            - Real.cos (t * (x + y))) / Real.sinh t)
          * (zy * conj zx) := by
  calc
    ((2 * t : Real) : Complex) * bombieriKstar x y t * zy
        * (((1 / 4 + x ^ 2 : Real) : Complex) * conj zx)
      = (((1 / 4 + x ^ 2 : Real) : Complex)
          * (((2 * t : Real) : Complex) * bombieriKstar x y t))
          * (zy * conj zx) := by ring
    _ = (Complex.ofReal (1 / 4 + x * y) * winInt t (y - x)
          - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
              - Real.cos (t * (x + y))) / Real.sinh t))
          * (zy * conj zx) := by
            rw [weighted_twoT_bombieriKstar x y t ht]
    _ = Complex.ofReal (1 / 4 + x * y) * winInt t (y - x)
          * (zy * conj zx)
        - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
            - Real.cos (t * (x + y))) / Real.sinh t)
          * (zy * conj zx) := by ring

/-- FLAGSHIP (slice 12g): the finite weighted `K*` Gram sum is precisely the
Wirtinger Q-form of the (8.5) exponential sum minus Bombieri's endpoint
correction.  This is the finite algebra content of (8.11). -/
theorem bombieriKstarGram_eq_qIntegrand_sub_endpointCorrection (t : Real)
    (ht : 0 < t) (gamma : Fin n -> Real) (z : Fin n -> Complex) :
    bombieriKstarGram t gamma z
      = (∫ x in -t..t,
          qIntegrand (expSum gamma z) (expSum gamma (dcoef gamma z)) x)
        - endpointCorrection t gamma z := by
  have hentry : ∀ i j : Fin n,
      ((2 * t : Real) : Complex) * bombieriKstar (gamma i) (gamma j) t
          * z j * (((1 / 4 + gamma i ^ 2 : Real) : Complex) * conj (z i))
        = Complex.ofReal (1 / 4 + gamma i * gamma j)
            * winInt t (gamma j - gamma i) * (z j * conj (z i))
          - Complex.ofReal ((Real.cosh t
                * Real.cos (t * (gamma i - gamma j))
              - Real.cos (t * (gamma i + gamma j))) / Real.sinh t)
            * (z j * conj (z i)) := by
    intro i j
    exact weighted_entry t ht (gamma i) (gamma j) (z i) (z j)
  calc
    bombieriKstarGram t gamma z
      = ∑ i, ∑ j, (Complex.ofReal (1 / 4 + gamma i * gamma j)
          * winInt t (gamma j - gamma i) * (z j * conj (z i))
        - Complex.ofReal ((Real.cosh t
              * Real.cos (t * (gamma i - gamma j))
            - Real.cos (t * (gamma i + gamma j))) / Real.sinh t)
          * (z j * conj (z i))) := by
            unfold bombieriKstarGram
            simp only [hentry]
    _ = (∑ i, ∑ j, Complex.ofReal (1 / 4 + gamma i * gamma j)
          * winInt t (gamma j - gamma i) * (z j * conj (z i)))
        - (∑ i, ∑ j, Complex.ofReal ((Real.cosh t
              * Real.cos (t * (gamma i - gamma j))
            - Real.cos (t * (gamma i + gamma j))) / Real.sinh t)
          * (z j * conj (z i))) := by
            simp only [Finset.sum_sub_distrib]
    _ = (∫ x in -t..t,
          qIntegrand (expSum gamma z) (expSum gamma (dcoef gamma z)) x)
        - endpointCorrection t gamma z := by
            rw [qChannel_swap, correctionChannel_swap,
              ← expSum_qIntegrand_mass t ht.le,
              kernelEndpointCorrection_eq_endpointCorrection t ht gamma z]

/-- The (7.4) eigen-relation transported all the way to the finite (8.11)
right side.  It remains division-free in `Lam`. -/
theorem bombieriEigen_gram_total (t : Real) (ht : 0 < t)
    (gamma : Fin n -> Real) (z : Fin n -> Complex) (Lam : Complex)
    (h : bombieriWOfZ gamma z
        = Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)) :
    (∑ i, bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i))
      = Lam * ((∫ x in -t..t,
          qIntegrand (expSum gamma z) (expSum gamma (dcoef gamma z)) x)
        - endpointCorrection t gamma z) := by
  calc
    (∑ i, bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i))
      = Lam * bombieriKstarGram t gamma z := by
          simpa only [bombieriKstarGram] using bombieriEigen_gram t gamma z Lam h
    _ = Lam * ((∫ x in -t..t,
          qIntegrand (expSum gamma z) (expSum gamma (dcoef gamma z)) x)
        - endpointCorrection t gamma z) := by
          rw [bombieriKstarGram_eq_qIntegrand_sub_endpointCorrection t ht]

end C1BombieriSection8TotalAssembly
end Source
end ConnesWeilRH
