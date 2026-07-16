/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct

/-!
# Commutation of the synchronized finite Euler generator

The common-log prime contractions are translations in one additive
representation.  This module lifts their concrete commutation through the
Neumann inverses and proves that the right logarithmic derivative of the
complete ordered Euler product is the finite sum of the one-prime resolvent
generators.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedEulerCommutation

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerProduct

/-- An unscaled prime contraction commutes with every synchronized scalar
multiple of another prime contraction. -/
theorem primeContraction_commute_parameterizedContraction
    (alpha : ℝ) (p q : CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerContraction p)
      (parameterizedPrimeEulerContraction alpha q) := by
  unfold parameterizedPrimeEulerContraction
  change ccm24PrimeEulerContraction p *
      ((alpha : ℂ) • ccm24PrimeEulerContraction q) =
    ((alpha : ℂ) • ccm24PrimeEulerContraction q) *
      ccm24PrimeEulerContraction p
  simpa only [mul_smul_comm, smul_mul_assoc] using
    congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      (alpha : ℂ) • T) (ccm24PrimeEulerContraction_commute p q).eq

/-- Parameterized prime contractions commute at arbitrary synchronized
parameters. -/
theorem parameterizedPrimeEulerContraction_commute
    (alpha beta : ℝ) (p q : CCM24VisiblePrime) :
    Commute (parameterizedPrimeEulerContraction alpha p)
      (parameterizedPrimeEulerContraction beta q) := by
  unfold parameterizedPrimeEulerContraction
  change ((alpha : ℂ) • ccm24PrimeEulerContraction p) *
      ((beta : ℂ) • ccm24PrimeEulerContraction q) =
    ((beta : ℂ) • ccm24PrimeEulerContraction q) *
      ((alpha : ℂ) • ccm24PrimeEulerContraction p)
  calc
    ((alpha : ℂ) • ccm24PrimeEulerContraction p) *
        ((beta : ℂ) • ccm24PrimeEulerContraction q) =
        (alpha : ℂ) • (ccm24PrimeEulerContraction p *
          ((beta : ℂ) • ccm24PrimeEulerContraction q)) := by
      rw [smul_mul_assoc]
    _ = (alpha : ℂ) • (((beta : ℂ) •
          ccm24PrimeEulerContraction q) *
          ccm24PrimeEulerContraction p) := by
      congr 1
      simpa only [parameterizedPrimeEulerContraction] using
        (primeContraction_commute_parameterizedContraction beta p q).eq
    _ = ((beta : ℂ) • ccm24PrimeEulerContraction q) *
        ((alpha : ℂ) • ccm24PrimeEulerContraction p) := by
      rw [mul_smul_comm]

/-- An actual prime contraction commutes with the full Neumann inverse of
every parameterized prime factor. -/
theorem primeContraction_commute_parameterizedPrimeEulerInverse
    (alpha : ℝ) (p q : CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerContraction p)
      (parameterizedPrimeEulerInverse alpha q) := by
  unfold parameterizedPrimeEulerInverse
  exact Commute.tsum_right _ (fun n =>
    (primeContraction_commute_parameterizedContraction alpha p q).pow_right n)

/-- Every parameterized factor commutes with every prime contraction. -/
theorem parameterizedPrimeEulerFactor_commute_primeContraction
    (alpha : ℝ) (p q : CCM24VisiblePrime) :
    Commute (parameterizedPrimeEulerFactor alpha p)
      (ccm24PrimeEulerContraction q) := by
  unfold parameterizedPrimeEulerFactor
  exact (Commute.one_left _).sub_left
    (primeContraction_commute_parameterizedContraction alpha q p).symm

/-- Every parameterized factor commutes with every Neumann inverse. -/
theorem parameterizedPrimeEulerFactor_commute_inverse
    (alpha beta : ℝ) (p q : CCM24VisiblePrime) :
    Commute (parameterizedPrimeEulerFactor alpha p)
      (parameterizedPrimeEulerInverse beta q) := by
  unfold parameterizedPrimeEulerFactor parameterizedPrimeEulerInverse
  apply Commute.tsum_right
  intro n
  exact ((Commute.one_left _).sub_left
    (parameterizedPrimeEulerContraction_commute alpha beta p q)).pow_right n

/-- A parameterized Euler factor commutes with every one-prime right
generator. -/
theorem parameterizedPrimeEulerFactor_commute_generator
    (alpha beta : ℝ) (p q : CCM24VisiblePrime) :
    Commute (parameterizedPrimeEulerFactor alpha p)
      (parameterizedPrimeEulerGenerator beta q) := by
  unfold parameterizedPrimeEulerGenerator
  exact
    (parameterizedPrimeEulerFactor_commute_primeContraction alpha p q).neg_right.mul_right
      (parameterizedPrimeEulerFactor_commute_inverse alpha beta p q)

/-- The resolvent generators at any two visible primes commute. -/
theorem parameterizedPrimeEulerGenerator_commute
    (alpha beta : ℝ) (p q : CCM24VisiblePrime) :
    Commute (parameterizedPrimeEulerGenerator alpha p)
      (parameterizedPrimeEulerGenerator beta q) := by
  unfold parameterizedPrimeEulerGenerator
  have hac : Commute (-ccm24PrimeEulerContraction p)
      (-ccm24PrimeEulerContraction q) :=
    (ccm24PrimeEulerContraction_commute p q).neg_left.neg_right
  have had : Commute (-ccm24PrimeEulerContraction p)
      (parameterizedPrimeEulerInverse beta q) :=
    (primeContraction_commute_parameterizedPrimeEulerInverse beta p q).neg_left
  have hbc : Commute (parameterizedPrimeEulerInverse alpha p)
      (-ccm24PrimeEulerContraction q) :=
    (primeContraction_commute_parameterizedPrimeEulerInverse alpha q p).symm.neg_right
  have hbd : Commute (parameterizedPrimeEulerInverse alpha p)
      (parameterizedPrimeEulerInverse beta q) := by
    unfold parameterizedPrimeEulerInverse
    apply Commute.tsum_left
    intro m
    apply Commute.tsum_right
    intro n
    exact
      (parameterizedPrimeEulerContraction_commute alpha beta p q).pow_pow m n
  exact (hac.mul_right had).mul_left (hbc.mul_right hbd)

/-- One Euler factor commutes with the complete finite additive generator. -/
theorem parameterizedPrimeEulerFactor_commute_finiteGenerator
    (alpha beta : ℝ) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    Commute (parameterizedPrimeEulerFactor alpha p)
      (parameterizedFiniteEulerGenerator beta S) := by
  induction S with
  | nil =>
      rw [parameterizedFiniteEulerGenerator_nil]
      exact Commute.zero_right _
  | cons q S ih =>
      rw [parameterizedFiniteEulerGenerator_cons]
      exact (parameterizedPrimeEulerFactor_commute_generator alpha beta p q).add_right ih

/-- The finite additive generator multiplied by the complete Euler product
is exactly the product-rule derivative.  All prime channels remain inside the
finite operator sum until this algebraic identity is complete. -/
theorem parameterizedFiniteEulerGenerator_mul_factor
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedFiniteEulerGenerator alpha S *
        parameterizedFiniteEulerFactor alpha S =
      parameterizedFiniteEulerDerivative alpha S := by
  induction S with
  | nil =>
      simp [parameterizedFiniteEulerGenerator,
        parameterizedFiniteEulerFactor, parameterizedFiniteEulerDerivative]
  | cons p S ih =>
      rw [parameterizedFiniteEulerGenerator_cons,
        parameterizedFiniteEulerFactor, parameterizedFiniteEulerDerivative]
      have hcomm :=
        parameterizedPrimeEulerFactor_commute_finiteGenerator alpha alpha p S
      have hprime := parameterizedPrimeEulerGenerator_mul_factor alpha p halpha
      have hprime' : parameterizedPrimeEulerGenerator alpha p *
          parameterizedPrimeEulerFactor alpha p =
          -ccm24PrimeEulerContraction p := by
        simpa only [parameterizedPrimeEulerFactor] using hprime
      have hhead : parameterizedPrimeEulerGenerator alpha p *
            (parameterizedPrimeEulerFactor alpha p *
              parameterizedFiniteEulerFactor alpha S) =
          (parameterizedPrimeEulerGenerator alpha p *
              parameterizedPrimeEulerFactor alpha p) *
            parameterizedFiniteEulerFactor alpha S :=
        (mul_assoc _ _ _).symm
      have htail : parameterizedFiniteEulerGenerator alpha S *
            (parameterizedPrimeEulerFactor alpha p *
              parameterizedFiniteEulerFactor alpha S) =
          parameterizedPrimeEulerFactor alpha p *
            (parameterizedFiniteEulerGenerator alpha S *
              parameterizedFiniteEulerFactor alpha S) :=
        (hcomm.left_comm _).symm
      calc
        (parameterizedPrimeEulerGenerator alpha p +
              parameterizedFiniteEulerGenerator alpha S) *
            (parameterizedPrimeEulerFactor alpha p *
              parameterizedFiniteEulerFactor alpha S) =
            (parameterizedPrimeEulerGenerator alpha p *
                parameterizedPrimeEulerFactor alpha p) *
                parameterizedFiniteEulerFactor alpha S +
              parameterizedPrimeEulerFactor alpha p *
                (parameterizedFiniteEulerGenerator alpha S *
                  parameterizedFiniteEulerFactor alpha S) := by
          rw [add_mul]
          exact congrArg₂ (· + ·) hhead htail
        _ = -ccm24PrimeEulerContraction p *
                parameterizedFiniteEulerFactor alpha S +
              parameterizedPrimeEulerFactor alpha p *
                parameterizedFiniteEulerDerivative alpha S := by
          rw [hprime', ih]

/-- The same-object right logarithmic derivative of the complete finite Euler
product is exactly the additive finite-prime resolvent generator. -/
theorem parameterizedFiniteEulerRightGenerator_eq_additiveGenerator
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedFiniteEulerRightGenerator alpha S =
      parameterizedFiniteEulerGenerator alpha S := by
  calc
    parameterizedFiniteEulerRightGenerator alpha S =
        parameterizedFiniteEulerDerivative alpha S *
          parameterizedFiniteEulerInverse alpha S := rfl
    _ = (parameterizedFiniteEulerGenerator alpha S *
          parameterizedFiniteEulerFactor alpha S) *
          parameterizedFiniteEulerInverse alpha S := by
        rw [parameterizedFiniteEulerGenerator_mul_factor alpha S halpha]
    _ = parameterizedFiniteEulerGenerator alpha S := by
        rw [mul_assoc,
          parameterizedFiniteEulerFactor_mul_inverse alpha S halpha, mul_one]

end CCM24FiniteSParameterizedEulerCommutation
end CCM25Concrete
end Source
end ConnesWeilRH
