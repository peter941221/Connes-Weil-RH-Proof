/-
Mellin-step probe (parallel source model): the **logarithmic change of
variables** underpinning the additive-log Mellin convolution.

`mellin (fun t => h t) s = ∫ t∈Ioi 0, t^(s-1) • h t`.  The Mellin-product law
this project lacks is proved by substituting `t = e^u` (additive log
coordinate).  This probe proves the elementary transport lemma that turns an
integral over `Ioi 0` into the log-coordinate form over `ℝ`, using mathlib's
one-dimensional change-of-variables:

    ∫ x in (Real.exp '' univ) g x = ∫ u in ℝ, |Real.exp.deriv u| • g (Real.exp u)

with `Real.exp '' univ = Ioi 0` (`Real.range_exp`) and deriv `exp = exp`.

Proof-of-PIPELINE only: verifies the log-transport block is available and
build-clean; later modules build the Mellin convolution identity on top.

- No RH claim.  No sorries.  Target axioms `[propext, Classical.choice,
  Quot.sound]`.
-/

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinLogLiftProbe

open MeasureTheory MeasureTheory.Measure Metric Filter Set
open scoped Topology

/-- The real-exponential image of `univ` is the positive halfline `Ioi 0`. -/
lemma exp_image_univ_eq_Ioi : Real.exp '' (Set.univ : Set ℝ) = Set.Ioi (0 : ℝ) := by
  rw [image_univ, Real.range_exp]

/-- Transport an integral over `Ioi 0` to the log coordinate:
`∫_Ioi 0 g = ∫_ℝ (exp u) • g (exp u) du`.  This is the change `t = e^u`,
`dt = e^u du` (one-dimensional change-of-variables, `JacobianOneDim`). -/
theorem integral_Ioi_eq_integral_exp_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    (∫ x in Ioi (0 : ℝ), g x) =
      (∫ u : ℝ in Set.univ, (Real.exp u) • g (Real.exp u)) := by
  -- change-of-variables: ∫ over (exp '' univ) of g = ∫ over univ of |exp'| • (g∘exp)
  calc
    ∫ x in Ioi (0 : ℝ), g x
        = ∫ x in Real.exp '' (Set.univ : Set ℝ), g x := by
          rw [exp_image_univ_eq_Ioi]
    _ = ∫ u in Set.univ, (Real.exp u) • g (Real.exp u) := by
          rw [integral_image_eq_integral_abs_deriv_smul
            (s := (Set.univ : Set ℝ)) (f := Real.exp)
            (by exact MeasurableSet.univ)
            (by intro x _hx; exact (Real.hasDerivAt_exp x).hasDerivWithinAt)
            (by exact Real.exp_injective.injOn) g]
          congr 1
          funext u
          simp [Real.exp_pos u]  -- |exp u| = exp u

end MellinLogLiftProbe
end Dev
end Source
end ConnesWeilRH