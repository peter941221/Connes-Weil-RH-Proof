import ConnesWeilRH.Dev.R1Step4Probe982
import ConnesWeilRH.Dev.R1Step5Probe983
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData

/-!
# R1 step 7 — on-index-set retype seam for the `atoms` field (985)

The production certificate currently stores
`SourceFinitePrimeArithmeticNormalizationForSourceTest`, which asks for data
at every natural number.  Its source-index field then asks for `IsPrimePow n`
even when `n` is outside the finite global prime index set.  This is the L653
quantifier-scope wall.

This probe does not change the production API.  It introduces the smallest
candidate replacement: source-test arithmetic data is required only for
`n ∈ W.globalPrimeIndexSet`.  On the concrete `{2}` carrier, the candidate is
constructed from the existing reduce-lane object `gd_reduce`, with the source
test read-off proved definitionally.

The result is a retype seam, not a complete `CommonFinitePrimeArithmeticSourceData`
construction.  It does not prove SourceRH or RH, and adds no axioms.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace R1Step7Probe985

open L657DiagProbe
open R1StepTransformProbe982
open R1Step5Probe983
open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CCM25Concrete.PrimePowerTest
open ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic

structure SourceFinitePrimeArithmeticDataOnGlobalIndexSet
    (W : WeilFormSymbols) (f g : TestFunction)
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) where
  atIndex :
    ∀ n : ℕ, n ∈ W.globalPrimeIndexSet →
      SourceFinitePrimeArithmeticDataForSourceTest W f g sourceTest n

noncomputable def concreteGlobalData :
    SourceFinitePrimeArithmeticDataOnGlobalIndexSet W0 f0 f0 sourceIface where
  atIndex := fun n hn =>
    { data := gd_reduce.atIndex n hn
      sourceTestReadOff := by
        rfl }

lemma concreteGlobalData_at_two (h : 2 ∈ W0.globalPrimeIndexSet) :
    (concreteGlobalData.atIndex 2 h).data = gd_reduce.atIndex 2 h := by
  rfl

lemma concreteGlobalData_source_test (n : ℕ)
    (hn : n ∈ W0.globalPrimeIndexSet) :
    (concreteGlobalData.atIndex n hn).data.sourceTest = sourceIface := by
  exact (concreteGlobalData.atIndex n hn).sourceTestReadOff

lemma concreteGlobalData_exists :
    Nonempty
      (SourceFinitePrimeArithmeticDataOnGlobalIndexSet W0 f0 f0 sourceIface) :=
  ⟨concreteGlobalData⟩

#print axioms concreteGlobalData
#print axioms concreteGlobalData_at_two
#print axioms concreteGlobalData_source_test
#print axioms concreteGlobalData_exists

end R1Step7Probe985
end Dev
end Source
end ConnesWeilRH
