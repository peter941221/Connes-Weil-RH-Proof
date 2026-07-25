/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualJuliaRangeSineDouglas
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization

/-!
# Scalar guard between Julia range-sine and ambient-loss scales

Proof 550 identifies the weighted range-sine obligation with a Douglas factor
through the actual canonical Schur defect. Proof 506 constructs an explicit
ambient antiresonant loss column. Their scalar normalizations are not the
same: the range-sine row carries sqrt(p - 1), while the ambient loss column
carries sqrt(p^(-1/2)) / (1 + p^(-1/2)).

This module formalizes that mismatch so the ambient-loss factor cannot be
silently reused as the missing range-sine producer. It is a guard only, not
a Gate 3U proof.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineDouglas
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSJuliaCausal

theorem primeJuliaWeight_ge_one (p : CCM24VisiblePrime) :
    1 ≤ primeJuliaWeight p := by
  unfold primeJuliaWeight
  have hp : (2 : ℕ) ≤ p := Nat.succ_le_of_lt p.property
  have hpReal : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp
  linarith

theorem ccm24PrimeEulerCoefficient_pos (p : CCM24VisiblePrime) :
    0 < ccm24PrimeEulerCoefficient p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one p.property)
  have hsqrt : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp0
  unfold ccm24PrimeEulerCoefficient
  exact div_pos zero_lt_one hsqrt

theorem primeEulerAmbientLossScale_lt_one (p : CCM24VisiblePrime) :
    primeEulerAmbientLossScale p < 1 := by
  let a := ccm24PrimeEulerCoefficient p
  have hpos : 0 < a := ccm24PrimeEulerCoefficient_pos p
  have hnonneg : 0 ≤ a := le_of_lt hpos
  have hlt : a < 1 := ccm24PrimeEulerCoefficient_lt_one p
  have hsqrt_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt hnonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsqrt_lt_one : Real.sqrt a < 1 := by
    nlinarith
  have hden : 0 < 1 + a := by linarith
  have hnum_lt_den : Real.sqrt a < 1 + a := by linarith
  unfold primeEulerAmbientLossScale
  exact (div_lt_one hden).2 hnum_lt_den

theorem primeEulerAmbientLossScale_nonneg (p : CCM24VisiblePrime) :
    0 ≤ primeEulerAmbientLossScale p := by
  let a := ccm24PrimeEulerCoefficient p
  have hpos : 0 < a := ccm24PrimeEulerCoefficient_pos p
  have hden : 0 < 1 + a := by linarith
  unfold primeEulerAmbientLossScale
  exact div_nonneg (Real.sqrt_nonneg _) (le_of_lt hden)

theorem primeEulerAmbientLossScale_sq_lt_one (p : CCM24VisiblePrime) :
    primeEulerAmbientLossScale p ^ 2 < 1 := by
  have hnonneg := primeEulerAmbientLossScale_nonneg p
  have hlt := primeEulerAmbientLossScale_lt_one p
  nlinarith

/-- The ambient-loss square scale is strictly smaller than the Julia
range-sine weight. -/
theorem primeEulerAmbientLossScale_sq_lt_primeJuliaWeight
    (p : CCM24VisiblePrime) :
    primeEulerAmbientLossScale p ^ 2 < primeJuliaWeight p := by
  have hscale := primeEulerAmbientLossScale_sq_lt_one p
  have hweight := primeJuliaWeight_ge_one p
  linarith

theorem primeEulerAmbientLossScale_sq_ne_primeJuliaWeight
    (p : CCM24VisiblePrime) :
    primeEulerAmbientLossScale p ^ 2 ≠ primeJuliaWeight p :=
  ne_of_lt (primeEulerAmbientLossScale_sq_lt_primeJuliaWeight p)

/-- The ambient-loss scalar is not the scalar normalizer required by the
Proof 550 weighted range-sine Douglas row. -/
theorem primeEulerAmbientLossScale_ne_sqrt_primeJuliaWeight
    (p : CCM24VisiblePrime) :
    primeEulerAmbientLossScale p ≠ Real.sqrt (primeJuliaWeight p) := by
  intro h
  have hsq := congrArg (fun x : ℝ => x ^ 2) h
  have hsqrt :
      Real.sqrt (primeJuliaWeight p) ^ 2 = primeJuliaWeight p :=
    Real.sq_sqrt (primeJuliaWeight_nonneg p)
  exact primeEulerAmbientLossScale_sq_ne_primeJuliaWeight p
    (by simpa only [hsqrt] using hsq)

end CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
end CCM25Concrete
end Source
end ConnesWeilRH
