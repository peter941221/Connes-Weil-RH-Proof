import ConnesWeilRH.Source.AnalyticCore

namespace ConnesWeilRH
namespace Dev
namespace PerCommonCarrierFeasibilityProbe

open Source
open Source.AnalyticCore

/--
Contrapositive of the retained FORWARD `∀ F` witness of
`PerCommonSourceFinitePrimeSupport` (AnalyticCore.lean:7468): an index outside
the finite carrier `globalIndexSet` is invisible -- its prime term is zero for
EVERY test.  This pins the residual structural gap that the S2 per-common
refactor (docs/proofs/835) did NOT close: the forward direction is still
quantified over all tests, so finiteness of the carrier is a load-bearing data
obligation, not a proven fact.  Replacing the L137 axiom needs a real nonzero
prime-term witness (arithmetic data), not a shape change.  Axiom-clean.
-/
theorem invisible_outside_carrier
    (A : SourceTestAlgebra) (E : SourceEvaluationData A) (common : A.Test)
    (S : PerCommonSourceFinitePrimeSupport A E common)
    (n : Nat) (hnOut : n ∉ S.globalIndexSet) (F : A.Test) :
    E.sourceFinitePrimeTerm n F = 0 := by
  by_contra hnz
  have hMem : n ∈ S.globalIndexSet := S.sourceVisibleGlobalIndex n F hnz
  exact hnOut hMem

end PerCommonCarrierFeasibilityProbe
end Dev
end ConnesWeilRH