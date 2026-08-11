import ConnesWeilRH.Dev.L657DiagProbe
import ConnesWeilRH.Dev.R1Step5Probe983b_balance
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData

/-!
# R1 step 6 — `CommonFinitePrimeArithmeticSourceData` is uninhabited at the
common test f0 (984)

Probe 983b refuted the analytic leaf
`SourceScopedArchimedeanContributionBalance W0 f0 λ gd rd` at the drained
window λ = 0 (and hence the whole `∀λ` family on the concrete carrier).  This
probe makes the *assembly* consequence explicit:

`CommonFinitePrimeArithmeticSourceData W0` requires a field

    scopedArchimedeanContributionBalance :
      ∀ λ, ∀ globalData, ∀ restrictedData,
        SourceScopedArchimedeanContributionBalance W0 commonTestFunction λ
          globalData restrictedData

which, at `commonTestFunction = f0` and `λ = 0`, instantiates over the very
`gd` / `rd` objects whose balance `L657DiagProbe` refutes.  Therefore any
`CommonFinitePrimeArithmeticSourceData W0` with `commonTestFunction = f0` is
inconsistent — the "wire the reduce-lane into `ccm25ArithmeticPackage`" seam
(984 target) is blocked *structurally* on the concrete `{2}` carrier.

This is honest negative evidence, not a closure: it pins that the balance leaf
is a REFUTED prerequisite of the package, so the route keeps needing the
canonical-Weil sign repair (847b/912 seam) business — it is NOT an analysis
gap one can close locally on the concrete model.

Zero `sorry`, no new `axiom`.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace R1Step6Probe984

open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
open ConnesWeilRH.Source.Dev.L657DiagProbe

/-- The `CommonFinitePrimeArithmeticSourceData` at `commonTestFunction = f0`
is empty: its `scopedArchimedeanContributionBalance` field is refuted at λ=0
over the concrete `gd`/`rd` objects. -/
theorem common_source_data_f0_uninhabited
    (h : CommonFinitePrimeArithmeticSourceData W0)
    (hcomm : h.commonTestFunction = f0) : False := by
  rcases h with ⟨commonTestFunction, finitePrimeData, scopedArchimedeanContributionBalance⟩
  subst hcomm
  -- instantiate the field at λ=0 with the concrete global/restricted objects
  exact L657DiagProbe.probe_balance_false
    (scopedArchimedeanContributionBalance (0 : ℝ) gd rd)

/-- Corollary: no `CommonFinitePrimeArithmeticSourceData W0` can use the common
bump as its common test — the reduce-lane package seam is blocked on the
concrete `{2}` carrier. -/
theorem no_common_source_data_with_f0 :
    ¬ (∃ h : CommonFinitePrimeArithmeticSourceData W0, h.commonTestFunction = f0) := by
  intro h
  rcases h with ⟨h, hcomm⟩
  exact common_source_data_f0_uninhabited h hcomm

#print axioms common_source_data_f0_uninhabited
#print axioms no_common_source_data_with_f0

end R1Step6Probe984
end Dev
end Source
end ConnesWeilRH