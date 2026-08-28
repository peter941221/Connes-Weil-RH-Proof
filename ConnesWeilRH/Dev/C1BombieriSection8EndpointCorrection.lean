/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8KernelWeights

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, seventeenth slice: endpoint correction factorization

This leaf factors the elementary correction channel of the weighted (7.1)
kernel entry through the two endpoint values of the finite exponential sum.
For `Z(u) = Σ exp(-i gamma u) z_gamma`, its target boundary expression is

```
 (e^t + e^-t)/(2(e^t-e^-t)) (Z(t) conj Z(t) + Z(-t) conj Z(-t))
 - 1/(e^t-e^-t) (Z(t) conj Z(-t) + conj Z(t) Z(-t)).
```

The first declarations establish the finite-product and scalar engines used
by the final double-sum factorization.  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8EndpointCorrection

open ConnesWeilRH.Source.C1BombieriSection8ExpMass
open ConnesWeilRH.Source.C1BombieriSection8ExpSum
open ConnesWeilRH.Source.C1BombieriSection8KernelWeights
open scoped ComplexConjugate

variable {n : Nat}

/-- The endpoint correction in Bombieri's (8.11) shape, written with the
real-symmetric cross term required by the even/odd recombination. -/
noncomputable def endpointCorrection (t : Real) (gamma : Fin n → Real)
    (z : Fin n → Complex) : Complex :=
  Complex.ofReal ((Real.exp t + Real.exp (-t))
      / (2 * (Real.exp t - Real.exp (-t))))
      * (expSum gamma z t * conj (expSum gamma z t)
        + expSum gamma z (-t) * conj (expSum gamma z (-t)))
    - Complex.ofReal (1 / (Real.exp t - Real.exp (-t)))
      * (expSum gamma z t * conj (expSum gamma z (-t))
        + conj (expSum gamma z t) * expSum gamma z (-t))

/-- The double-sum correction carried by the weighted (7.1) kernel entries. -/
noncomputable def kernelEndpointCorrection (t : Real) (gamma : Fin n → Real)
    (z : Fin n → Complex) : Complex :=
  ∑ i, ∑ j, Complex.ofReal ((Real.cosh t * Real.cos (t * (gamma i - gamma j))
      - Real.cos (t * (gamma i + gamma j))) / Real.sinh t)
    * (z i * conj (z j))

/-- Product expansion at two arbitrary endpoints.  The conjugated second
sum reverses its phase, leaving the phase `gamma_j*v - gamma_i*u` on each
finite Gram pair. -/
theorem expSum_endpoint_product (gamma : Fin n → Real) (z : Fin n → Complex)
    (u v : Real) :
    expSum gamma z u * conj (expSum gamma z v)
      = ∑ i, ∑ j, (z i * conj (z j))
          * Complex.exp (Complex.ofReal (gamma j * v - gamma i * u) * Complex.I) := by
  unfold expSum
  rw [map_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conj_mul_d, conj_expTerm]
  have harg : Complex.ofReal ((-(gamma i)) * u) * Complex.I
      + Complex.ofReal (gamma j * v) * Complex.I
      = Complex.ofReal (gamma j * v - gamma i * u) * Complex.I := by
    rw [← add_mul, ← Complex.ofReal_add]
    congr 1
    ring
  rw [mul_mul_mul_comm, ← Complex.exp_add, harg]
  ring

/-- A pair of opposite imaginary phases is twice its cosine component. -/
private theorem expI_add_neg (a : Real) :
    Complex.exp (Complex.ofReal a * Complex.I)
      + Complex.exp (Complex.ofReal (-a) * Complex.I)
      = Complex.ofReal (2 * Real.cos a) := by
  have hpos := exp_i_mul_real 1 a
  have hneg := exp_i_mul_real 1 (-a)
  rw [one_mul] at hpos hneg
  rw [hpos, hneg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  calc
    _ = (2 : Complex) * Complex.ofReal (Real.cos a) := by ring
    _ = Complex.ofReal (2 * Real.cos a) := by
      apply Complex.ext <;> simp

/-- The scalar coefficient behind the endpoint correction: after pairing
opposite phases, `(cosh*cos - cos)/sinh` is exactly the (8.11) pair of
endpoint coefficients. -/
private theorem correction_scalar (t a b : Real) (ht : 0 < t) :
    Complex.ofReal ((Real.cosh t * Real.cos a - Real.cos b) / Real.sinh t)
      = Complex.ofReal ((Real.exp t + Real.exp (-t))
            / (2 * (Real.exp t - Real.exp (-t))))
          * Complex.ofReal (2 * Real.cos a)
        - Complex.ofReal (1 / (Real.exp t - Real.exp (-t)))
          * Complex.ofReal (2 * Real.cos b) := by
  have hlt : Real.exp (-t) < Real.exp t :=
    Real.exp_lt_exp.mpr (by linarith)
  have hdiff : Real.exp t - Real.exp (-t) ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  have hreal : (Real.cosh t * Real.cos a - Real.cos b) / Real.sinh t
      = ((Real.exp t + Real.exp (-t)) / (2 * (Real.exp t - Real.exp (-t))))
          * (2 * Real.cos a)
        - (1 / (Real.exp t - Real.exp (-t))) * (2 * Real.cos b) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    field_simp [hdiff]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  exact congrArg Complex.ofReal hreal

/-- One weighted (7.1) correction pair is the corresponding four endpoint
phases.  The two difference phases combine to `cos(t(x-y))`; the two sum
phases combine to `cos(t(x+y))`. -/
private theorem correction_pair_exp (t x y : Real) (ht : 0 < t)
    (zx zy : Complex) :
    Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
        - Real.cos (t * (x + y))) / Real.sinh t)
        * (zx * conj zy)
      = Complex.ofReal ((Real.exp t + Real.exp (-t))
            / (2 * (Real.exp t - Real.exp (-t))))
          * ((zx * conj zy)
                * Complex.exp (Complex.ofReal ((y - x) * t) * Complex.I)
            + (zx * conj zy)
                * Complex.exp (Complex.ofReal ((x - y) * t) * Complex.I))
        - Complex.ofReal (1 / (Real.exp t - Real.exp (-t)))
          * ((zx * conj zy)
                * Complex.exp (Complex.ofReal (-((x + y) * t)) * Complex.I)
            + (zx * conj zy)
                * Complex.exp (Complex.ofReal ((x + y) * t) * Complex.I)) := by
  have hdiff : Complex.exp (Complex.ofReal ((y - x) * t) * Complex.I)
      + Complex.exp (Complex.ofReal (-((y - x) * t)) * Complex.I)
      = Complex.ofReal (2 * Real.cos (t * (x - y))) := by
    rw [expI_add_neg]
    congr 1
    have harg : (y - x) * t = -(t * (x - y)) := by ring
    rw [harg, Real.cos_neg]
  have hsum : Complex.exp (Complex.ofReal ((x + y) * t) * Complex.I)
      + Complex.exp (Complex.ofReal (-((x + y) * t)) * Complex.I)
      = Complex.ofReal (2 * Real.cos (t * (x + y))) := by
    convert expI_add_neg ((x + y) * t) using 1; ring
  rw [correction_scalar t (t * (x - y)) (t * (x + y)) ht,
    ← hdiff, ← hsum]
  ring

/-- Distribute two scalar endpoint channels through a finite double sum.
Keeping this bookkeeping lemma separate prevents the endpoint factorization
from depending on higher-order rewrite matching under two binders. -/
private theorem double_sum_linear (a b : Complex)
    (F G H I : Fin n → Fin n → Complex) :
    (∑ i, ∑ j, (a * (F i j + G i j) - b * (H i j + I i j)))
      = a * ((∑ i, ∑ j, F i j) + (∑ i, ∑ j, G i j))
        - b * ((∑ i, ∑ j, H i j) + (∑ i, ∑ j, I i j)) := by
  have pull (c : Complex) (P : Fin n → Fin n → Complex) :
      (∑ i, ∑ j, c * P i j) = c * (∑ i, ∑ j, P i j) := by
    symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun (i : Fin n) _ => ?_
    rw [Finset.mul_sum]
  have sum_add (P Q : Fin n → Fin n → Complex) :
      (∑ i, ∑ j, (P i j + Q i j))
        = (∑ i, ∑ j, P i j) + (∑ i, ∑ j, Q i j) := by
    calc
      (∑ i, ∑ j, (P i j + Q i j))
          = ∑ i, ((∑ j, P i j) + (∑ j, Q i j)) := by
              refine Finset.sum_congr rfl fun (i : Fin n) _ => ?_
              exact Finset.sum_add_distrib (s := Finset.univ)
                (f := fun j : Fin n => P i j) (g := fun j : Fin n => Q i j)
      _ = (∑ i, ∑ j, P i j) + (∑ i, ∑ j, Q i j) :=
        Finset.sum_add_distrib (s := Finset.univ)
          (f := fun i : Fin n => ∑ j, P i j)
          (g := fun i : Fin n => ∑ j, Q i j)
  have sum_sub (P Q : Fin n → Fin n → Complex) :
      (∑ i, ∑ j, (P i j - Q i j))
        = (∑ i, ∑ j, P i j) - (∑ i, ∑ j, Q i j) := by
    calc
      (∑ i, ∑ j, (P i j - Q i j))
          = ∑ i, ((∑ j, P i j) - (∑ j, Q i j)) := by
              refine Finset.sum_congr rfl fun (i : Fin n) _ => ?_
              exact Finset.sum_sub_distrib (s := Finset.univ)
                (f := fun j : Fin n => P i j) (g := fun j : Fin n => Q i j)
      _ = (∑ i, ∑ j, P i j) - (∑ i, ∑ j, Q i j) :=
        Finset.sum_sub_distrib (s := Finset.univ)
          (f := fun i : Fin n => ∑ j, P i j)
          (g := fun i : Fin n => ∑ j, Q i j)
  calc
    (∑ i, ∑ j, (a * (F i j + G i j) - b * (H i j + I i j)))
        = (∑ i, ∑ j, ((a * F i j + a * G i j)
            - (b * H i j + b * I i j))) := by
              refine Finset.sum_congr rfl fun (i : Fin n) _ => ?_
              refine Finset.sum_congr rfl fun (j : Fin n) _ => ?_
              ring
    _ = (∑ i, ∑ j, (a * F i j + a * G i j))
          - (∑ i, ∑ j, (b * H i j + b * I i j)) := by
            exact sum_sub _ _
    _ = (∑ i, ∑ j, a * F i j) + (∑ i, ∑ j, a * G i j)
          - ((∑ i, ∑ j, b * H i j) + (∑ i, ∑ j, b * I i j)) := by
            rw [sum_add, sum_add]
    _ = a * ((∑ i, ∑ j, F i j) + (∑ i, ∑ j, G i j))
          - b * ((∑ i, ∑ j, H i j) + (∑ i, ∑ j, I i j)) := by
            rw [pull a F, pull a G, pull b H, pull b I]
            ring

/-- FLAGSHIP (slice 12f): the correction double sum of the weighted (7.1)
kernel factors exactly into Bombieri's two endpoint products.  This is the
finite algebra bridge from the entry formula to the boundary term in (8.11). -/
theorem kernelEndpointCorrection_eq_endpointCorrection (t : Real) (ht : 0 < t)
    (gamma : Fin n → Real) (z : Fin n → Complex) :
    kernelEndpointCorrection t gamma z = endpointCorrection t gamma z := by
  have hTT : expSum gamma z t * conj (expSum gamma z t)
      = ∑ i, ∑ j, (z i * conj (z j))
          * Complex.exp (Complex.ofReal ((gamma j - gamma i) * t) * Complex.I) := by
    rw [expSum_endpoint_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    ring
  have hMM : expSum gamma z (-t) * conj (expSum gamma z (-t))
      = ∑ i, ∑ j, (z i * conj (z j))
          * Complex.exp (Complex.ofReal ((gamma i - gamma j) * t) * Complex.I) := by
    rw [expSum_endpoint_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    ring
  have hTM : expSum gamma z t * conj (expSum gamma z (-t))
      = ∑ i, ∑ j, (z i * conj (z j))
          * Complex.exp (Complex.ofReal (-((gamma i + gamma j) * t)) * Complex.I) := by
    rw [expSum_endpoint_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    ring
  have hMT : conj (expSum gamma z t) * expSum gamma z (-t)
      = ∑ i, ∑ j, (z i * conj (z j))
          * Complex.exp (Complex.ofReal ((gamma i + gamma j) * t) * Complex.I) := by
    calc
      conj (expSum gamma z t) * expSum gamma z (-t)
          = expSum gamma z (-t) * conj (expSum gamma z t) := by ring
      _ = ∑ i, ∑ j, (z i * conj (z j))
          * Complex.exp (Complex.ofReal ((gamma i + gamma j) * t) * Complex.I) := by
            rw [expSum_endpoint_product]
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 2
            ring
  have hpair : ∀ i j : Fin n,
      Complex.ofReal ((Real.cosh t * Real.cos (t * (gamma i - gamma j))
          - Real.cos (t * (gamma i + gamma j))) / Real.sinh t)
          * (z i * conj (z j))
        = Complex.ofReal ((Real.exp t + Real.exp (-t))
              / (2 * (Real.exp t - Real.exp (-t))))
            * ((z i * conj (z j))
                  * Complex.exp (Complex.ofReal ((gamma j - gamma i) * t) * Complex.I)
              + (z i * conj (z j))
                  * Complex.exp (Complex.ofReal ((gamma i - gamma j) * t) * Complex.I))
          - Complex.ofReal (1 / (Real.exp t - Real.exp (-t)))
            * ((z i * conj (z j))
                  * Complex.exp (Complex.ofReal (-((gamma i + gamma j) * t)) * Complex.I)
              + (z i * conj (z j))
                  * Complex.exp (Complex.ofReal ((gamma i + gamma j) * t) * Complex.I)) := by
    intro i j
    exact correction_pair_exp t (gamma i) (gamma j) ht (z i) (z j)
  unfold kernelEndpointCorrection endpointCorrection
  rw [hTT, hMM, hTM, hMT]
  simp only [hpair]
  exact double_sum_linear
    (a := Complex.ofReal ((Real.exp t + Real.exp (-t))
      / (2 * (Real.exp t - Real.exp (-t)))))
    (b := Complex.ofReal (1 / (Real.exp t - Real.exp (-t))))
    (F := fun i j => (z i * conj (z j))
      * Complex.exp (Complex.ofReal ((gamma j - gamma i) * t) * Complex.I))
    (G := fun i j => (z i * conj (z j))
      * Complex.exp (Complex.ofReal ((gamma i - gamma j) * t) * Complex.I))
    (H := fun i j => (z i * conj (z j))
      * Complex.exp (Complex.ofReal (-((gamma i + gamma j) * t)) * Complex.I))
    (I := fun i j => (z i * conj (z j))
      * Complex.exp (Complex.ofReal ((gamma i + gamma j) * t) * Complex.I))

end C1BombieriSection8EndpointCorrection
end Source
end ConnesWeilRH
