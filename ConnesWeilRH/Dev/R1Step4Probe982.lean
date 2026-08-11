import ConnesWeilRH.Dev.ConcreteP1SupportProbe
import ConnesWeilRH.Dev.L657DiagProbe
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmeticBridge

/-!
# R1 step 4 — the on-`{2}` arithmetic package: reduce-lane re-type seam

`L657DiagProbe` built the on-`{2}` `SourceGlobalFinitePrimeArithmeticData`
`gd` directly from the per-`2` atom.  This probe rebuilds the SAME global
arithmetic data through the documented "922 reduce lane"
(`SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData`), whose
pairing / weight / term read-offs are supplied AT THE SQUARE
`W.convolutionStar f f`, and proves the reduce-lane object agrees with the
direct per-`2` atom at the prime `2` — definitionally.

The `n ∈ W0.globalPrimeIndexSet` membership witnesses only need the exact
index-set fact `globalSetTwo` (an `rfl`-level equality), so the construction is
finite and axiom-clean.  This is the concrete content behind re-typing a
candidate certificate's `atomsWithSourceTest` onto the concrete evaluation
WITHOUT building a `∀ n : ℕ` normalization (the 653 wall).

RH NOT claimed.  Zero `sorry`.  No new `axiom`.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace R1StepTransformProbe982

open L657DiagProbe
open ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
open ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluation
open ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic

/-- The same global on-`{2}` arithmetic rebuilt through the documented reduce
lane `SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData` — the
`∀ n`-free entry point.  All membership witnesses are discharged by the exact
index set `{2}`; all read-offs at `2` are definitional on the concrete
carrier. -/
noncomputable def gd_reduce :
    SourceGlobalFinitePrimeArithmeticData W0 f0 f0 :=
  SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData
    (A := ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra)
    (E := E0)
    (W := W0)
    (common := common0)
    W0.globalPrimeIndexSet
    (fun n hn =>
      (by
        have h2 : n = 2 := by
          simpa [globalSetTwo] using hn
        subst h2
        exact isPrimePow_2))
    (fun n hn =>
      by
        have h2 : n = 2 := by
          simpa [globalSetTwo] using hn
        subst h2
        exact visible_two)
    (fun n hn =>
      by
        have h2 : n = 2 := by
          simpa [globalSetTwo] using hn
        subst h2
        rfl)
    (fun n hn => by
        have h2 : n = 2 := by
          simpa [globalSetTwo] using hn
        subst h2
        rfl)
    (fun n hn => by
        have h2 : n = 2 := by
          simpa [globalSetTwo] using hn
        subst h2
        rfl)

/-- The reduce-lane object at prime `2` agrees with the direct per-`2` atom:
the re-type seam is actually `rfl` (both read-offs are definitional on the
concrete carrier).  This is the load-bearing direction the 653 `atoms`
re-type needs: at the single visible prime, the reduce-lane arithmetic is the
same object as the direct atom. -/
lemma gd_reduce_at (n : ℕ) (hn : n ∈ W0.globalPrimeIndexSet) :
    (gd_reduce.atIndex n hn) = gd.atIndex n hn := by
  have h2 : n = 2 := by
    simpa [globalSetTwo] using hn
  subst h2
  rfl

/-- The reduce-lane object at the prime `2` agrees with the direct per-`2`
atom: the re-type seam is `rfl`. -/
lemma gd_reduce_at_two (h : 2 ∈ W0.globalPrimeIndexSet) :
    (gd_reduce.atIndex 2 h) = gd.atIndex 2 h := by
  rfl

/-- The global evaluator sums agree at the ``Mathlib`` level: the reduce-lane
object carries the same finite-prime arithmetic aggregate over `{2}` as the
direct object (each atom node acts on the same per-`2` data). -/
lemma gd_reduce_sMaxSum_eq_gd_maxSum :
    MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W0 f0 f0 gd_reduce =
      MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W0 f0 f0 gd := by
  simp [MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet,
        MathlibFinitePrimeEvaluatorSumOnIndexSet,
        MathlibFinitePrimeEvaluatorAtom, globalSetTwo, gd_reduce_at]

/-- The reduce-lane global sum is strictly positive: the on-`{2}` finite-prime
package is genuinely non-degenerate at the prime `2`. -/
theorem gd_reduce_global_sum_positive :
    0 < MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W0 f0 f0 gd_reduce := by
  rw [gd_reduce_sMaxSum_eq_gd_maxSum]
  exact L657DiagProbe.globalSum_positive

#print axioms gd_reduce
#print axioms gd_reduce_at
#print axioms gd_reduce_at_two
#print axioms gd_reduce_sMaxSum_eq_gd_maxSum
#print axioms gd_reduce_global_sum_positive

end R1StepTransformProbe982
end Dev
end Source
end ConnesWeilRH