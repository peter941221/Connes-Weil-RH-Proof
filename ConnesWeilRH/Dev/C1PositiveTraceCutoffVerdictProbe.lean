import ConnesWeilRH.Dev.C1PositiveTraceCutoffVerdict

/-!
# Probe for C1 positive-trace cutoff verdict

This probe audits the structural verdict on the plain-window cutoff family:
the raw cutoff traces are monotone, and the remainder-corrected readback
contract is uninhabited for every nonzero compact-log root.  It adds no new
analytic premise.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceCutoffVerdictProbe

#check C1PositiveTraceCutoffVerdict.cutoffPositiveBasisData_trace_re_monotone
#check C1PositiveTraceCutoffVerdict.not_nonempty_cutoffLimitContracts_of_test_ne_zero

#print axioms C1PositiveTraceCutoffVerdict.cutoffPositiveBasisData_trace_re_monotone
#print axioms C1PositiveTraceCutoffVerdict.not_nonempty_cutoffLimitContracts_of_test_ne_zero

end C1PositiveTraceCutoffVerdictProbe
end Dev
end Source
end ConnesWeilRH
