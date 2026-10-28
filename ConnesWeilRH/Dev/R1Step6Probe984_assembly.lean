import ConnesWeilRH.Dev.L657DiagProbe
import ConnesWeilRH.Dev.R1Step5Probe983b_balance
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData

/-!
# R1 step 6 — drained-window coverage boundary for common test f0 (984)

Probe 983b shows that the drained window λ = 0 does not cover the global prime
index set.  This probe records the corresponding assembly boundary:

`CommonFinitePrimeArithmeticSourceData W0` requires a field

      coverage -> SourceScopedArchimedeanContributionBalance ...

At `commonTestFunction = f0` and `λ = 0`, the coverage premise is false for
the concrete `{2}` carrier.  The scoped balance is therefore vacuous at this
drained parameter; this does not prove that
`CommonFinitePrimeArithmeticSourceData W0` is uninhabited.

This is honest boundary evidence, not a closure: the old unconditional balance
contract was too broad, while the new coverage-guarded contract excludes the
drained case.  The route still needs its canonical-Weil sign repair and the
remaining producer obligations; this probe does not claim SourceRH or RH.

Zero `sorry`, no new `axiom`.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace R1Step6Probe984

open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
open ConnesWeilRH.Source.Dev.L657DiagProbe

/-- The drained coverage guard is false for the concrete common test. -/
theorem common_source_data_f0_zero_coverage_false
    (h : CommonFinitePrimeArithmeticSourceData W0)
    (hcomm : h.commonTestFunction = f0) :
    ¬ W0.globalPrimeIndexSet ⊆ W0.restrictedPrimeIndexSet 0 := by
  exact L657DiagProbe.probe_coverage_false

/-- The concrete drained window is not a valid covered window. -/
theorem no_zero_coverage_for_f0 :
    ¬ W0.globalPrimeIndexSet ⊆ W0.restrictedPrimeIndexSet 0 := by
  exact L657DiagProbe.probe_coverage_false

#print axioms common_source_data_f0_zero_coverage_false
#print axioms no_zero_coverage_for_f0

end R1Step6Probe984
end Dev
end Source
end ConnesWeilRH
