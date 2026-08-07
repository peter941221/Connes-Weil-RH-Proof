import ConnesWeilRH.Source.AnalyticCore

namespace ConnesWeilRH
namespace Dev
namespace PerCommonCarrierExactnessProbe

open Source
open Source.AnalyticCore

/--
Per-common carrier forward-EXACTNESS: any index where `common` has a genuinely
nonzero prime term MUST lie in the finite carrier `globalPrimeIndexSet`.
This is the forward `∀F` witness specialized to `F = common`.
-/
theorem nonzero_common_term_mem
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test}
    (P : SourceFinitePrimeData A E common) (n : Nat)
    (hterm : E.sourceFinitePrimeTerm n common ≠ 0) :
    n ∈ P.globalPrimeIndexSet :=
  P.support.sourceVisibleGlobalIndex n common hterm

/--
The finite carrier exactly coincides with `common`'s prime-term VISIBLE index
support: membership iff the term is nonzero (both directions, no `IsPrimePow`
needed).  Combined with `globalIndexSet : Finset`, this means `common`'s
nontrivial prime terms live on a FINITE index set — the arithmetic vanishing the
real wire-up needs.
-/
theorem mem_iff_common_term_ne_zero
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (common : A.Test)
    (P : SourceFinitePrimeData A E common) (n : Nat) :
    n ∈ P.globalPrimeIndexSet <-> E.sourceFinitePrimeTerm n common ≠ 0 := by
  constructor
  · intro hn
    exact P.support.commonGlobalIndex n hn
  · intro hterm
    exact P.support.sourceVisibleGlobalIndex n common hterm

/-- The set of prime powers where `common` is nonzero is finite, because it
lives inside the finite carrier `P.globalPrimeIndexSet`. -/
theorem common_term_index_set_finite
    {A : SourceTestAlgebra} (E : SourceEvaluationData A) (common : A.Test)
    (P : SourceFinitePrimeData A E common) :
    Finite { n : Nat | E.sourceFinitePrimeTerm n common ≠ 0 } := by
  let carrier : Set ℕ := P.globalPrimeIndexSet
  have hsub : {n : ℕ | E.sourceFinitePrimeTerm n common ≠ 0} ⊆ carrier := by
    intro n hn
    exact (mem_iff_common_term_ne_zero common P n).2 hn
  exact (P.globalPrimeIndexSet.finite_toSet).subset hsub

end PerCommonCarrierExactnessProbe
end Dev
end ConnesWeilRH