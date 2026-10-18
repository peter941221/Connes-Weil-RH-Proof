import ConnesWeilRH.Dev.C1RouteBExteriorTermEnvelope2825
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_exterior_finite_sum_envelope2826
    {ι : Type} (s : Finset ι) (f B : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ B i) :
    |Finset.sum s f| ≤ Finset.sum s B := by
  classical
  have habs : |Finset.sum s f| ≤ Finset.sum s (fun i => |f i|) :=
    Finset.abs_sum_le_sum_abs f s
  exact habs.trans (Finset.sum_le_sum (fun i hi => hf i hi))

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
