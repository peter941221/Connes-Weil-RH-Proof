/-
Mellin-convolution identity, step A (parallel source model): the **log-coordinate
Mellin bridge**.  This is the genuinely new analytic block that the additive
`CompactLogTest.convolution` needs in order to satisfy the Mellin product law.

The plan (`docs/proofs/setup/plan-mellin-convolution-identity.md`) reduces the
product law `mellin(f ⋆_log g) = mellin(f)·mellin(g)` to three facts:

  (1) the log-coordinate Mellin bridge (this module):
          mellin (fun t => h (Real.log t)) s = ∫₀ (e^u)^s • h u
      i.e. an integral over `Ioi 0` in the multiplicative variable `t` carries
      exactly to an integral over `ℝ` in the additive log variable `u = log t`;
  (2) cpow-additivity to split exponentials, from `cpow_add`
      (`Mathlib.Analysis.SpecialFunctions.Pow.Complex`);
  (3) the Fubini reassociation `∫ (F ⋆ G) = (∫F)·(∫G)` for the additive-log
      convolution (`MeasureTheory.integral_convolution`).

This module establishes (1) for complex-valued `h` (the case the convolution
product law needs).  The transport `t = e^u`, `dt = e^u du` is reused verbatim
from `MellinLogLiftProbe.integral_Ioi_eq_integral_exp_smul`, and the weight
change `e^u · (e^u)^(s-1) = (e^u)^s` is proven from `cpow_add` together with
`Real.log (Real.exp u) = u`.

Convergence is carried by `MellinConvergent` (a Prop that is a terminating
witness, not an axiom).  There are no sorries; target axioms
`[propext, Classical.choice, Quot.sound]`.
-/

import ConnesWeilRH.Dev.MellinLogLiftProbe
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinConvolutionIdentity

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Filter Set
open Complex
open scoped Topology

/-- The product identity `e^u · (e^u)^(s-1) = (e^u)^s` as complex powers, true
because `cpow` of nonzero base is additive in the exponent and `x^(1:ℂ) = x`. -/
lemma exp_pow_add_pow_sub_one (u : ℝ) (s : ℂ) :
    (Real.exp u : ℂ) ^ (1 : ℂ) * (Real.exp u : ℂ) ^ (s - 1) =
      (Real.exp u : ℂ) ^ s := by
  have he : (Real.exp u : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_ne_zero u)
  have hsplit : (Real.exp u : ℂ) ^ (1 + (s - 1) : ℂ) =
      (Real.exp u : ℂ) ^ (1 : ℂ) * (Real.exp u : ℂ) ^ (s - 1) := by
    exact cpow_add (x := (Real.exp u : ℂ)) (1 : ℂ) (s - 1) he
  rw [← hsplit]
  congr 1
  ring_nf

/-- Combining the log-density `e^u` (the `dt = e^u du` factor) with the Mellin
weight `(e^u)^(s-1)` yields `(e^u)^s`, in the linear/multiplicative form
needed to reassociate the integrand. -/
theorem exp_pow_reassoc (u : ℝ) (s : ℂ) (z : ℂ) :
    (Real.exp u : ℂ) * ((Real.exp u : ℂ) ^ (s - 1) * z) =
      (Real.exp u : ℂ) ^ s * z := by
  rw [← mul_assoc]
  -- target only the leading factor, not the base inside `^(s-1)`
  nth_rewrite 1 [← cpow_one (Real.exp u : ℂ)]
  rw [exp_pow_add_pow_sub_one u s]

/-- The log-coordinate Mellin bridge, complex-valued `h`:

  `Mellin (fun t => h (Real.log t)) s = ∫_ℝ (e^u)^s • h u`.

This is the exact content of the change of variables `t = e^u`, `dt = e^u du`
applied to the Mellin integrand.  -/
theorem mellin_comp_log_eq_exp_integral (h : ℝ → ℂ) (s : ℂ) :
    mellin (fun ν : ℝ => h (Real.log ν)) s =
      ∫ u : ℝ in Set.univ, (Real.exp u : ℂ) ^ s • h u := by
  rw [mellin]
  calc
    (∫ ν in Ioi (0 : ℝ), (ν : ℂ) ^ (s - 1) • h (Real.log ν)) =
        ∫ u : ℝ in Set.univ,
          (Real.exp u) • ((Real.exp u : ℂ) ^ (s - 1) • h (Real.log (Real.exp u))) := by
          exact MellinLogLiftProbe.integral_Ioi_eq_integral_exp_smul
            (E := ℂ) (fun ν => (ν : ℂ) ^ (s - 1) • h (Real.log ν))
    _ = ∫ u : ℝ in Set.univ, (Real.exp u : ℂ) ^ s • h u := by
          apply integral_congr_ae
          filter_upwards with u
          have hlogu : Real.log (Real.exp u) = u := Real.log_exp u
          -- outer real scalar e^u and inner complex Mellin weight
          calc
            (Real.exp u) • ((Real.exp u : ℂ) ^ (s - 1) • h (Real.log (Real.exp u)))
                = (Real.exp u) • ((Real.exp u : ℂ) ^ (s - 1) • h u) := by
                  rw [hlogu]
            _ = (Real.exp u : ℂ) ^ s • h u := by
                  -- real scalar coercion: X • z = (X:ℂ) * (z:ℂ); inner complex
                  -- smul X • z = X * z via smul_eq_mul
                  rw [Complex.real_smul]
                  rw [smul_eq_mul, smul_eq_mul]
                  rw [exp_pow_reassoc]

end
end MellinConvolutionIdentity
end Dev
end Source
end ConnesWeilRH