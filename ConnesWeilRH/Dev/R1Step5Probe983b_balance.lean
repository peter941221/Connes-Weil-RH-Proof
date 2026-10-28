import ConnesWeilRH.Dev.L657DiagProbe

/-!
# R1 step 5b — drained-window coverage boundary (983b)

The analytic leaf

    SourceScopedArchimedeanContributionBalance W f lambda gd rd

is now a coverage-guarded equality of two scoped formulas:

    globalPrimeIndexSet ⊆ restrictedPrimeIndexSet lambda →

    SourceScopedRestrictedArchimedeanFormula W f lambda rd =
    SourceScopedGlobalArchimedeanFormula W f gd
    ─────────────────────────────────────────────────────────
    archimedeanTerm(f⋆f) + polePairing(f) − Σᵣ(λ) =
        poleFunctional(f⋆f) − archimedeanTerm(f⋆f) − Σ_g

On the concrete carrier `W0 = concreteWeilForm.toWeilFormSymbols`:

  - `W0.archimedeanTerm _ ≡ 0`        (`concreteWeilForm.archimedeanTerm := fun _ => 0`)
  - `W0.polePairing f0 = W0.poleFunctional (f0⋆f0)`   (`polePairingEqual`)

so the balance reduces to the index identity

    Σᵣ(λ) = Σ_g .

The carrier is a cut-off window (`perCommonSupport`):

| λ           | restrictedPrimeIndexSet λ | Σᵣ(λ)  | balance demands      |
|-------------|---------------------------|--------|----------------------|
| λ = 0 drain | ∅                         | 0      | coverage is false     |
| λ = 2 full  | `{2}`                      | Σ_g    | Σ_g = Σ_g  ✓        |

The drained `λ = 0` case does not satisfy the coverage guard because the
global carrier contains `2` while the restricted set is empty.  Therefore the
new balance proposition is vacuous at `λ = 0`; it does not claim that the
common source-data structure is uninhabited.  The old unconditional balance
refutation is superseded by `L657DiagProbe.probe_coverage_false`.

Zero `sorry`, no new `axiom`. RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace R1Step5Probe983b

open L657DiagProbe
open ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
open ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic
open ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
open ConnesWeilRH.Source.AnalyticCore

/-- The concrete drained window cannot cover the global prime index set. -/
theorem drained_coverage_impossible :
    W0.globalPrimeIndexSet ⊆ W0.restrictedPrimeIndexSet (0 : ℝ) → False := by
  exact L657DiagProbe.probe_coverage_false

/-- The coverage guard is false at the drained parameter. -/
theorem drained_window_not_covered :
    ¬ W0.globalPrimeIndexSet ⊆ W0.restrictedPrimeIndexSet (0 : ℝ) := by
  exact L657DiagProbe.probe_coverage_false

#print axioms drained_coverage_impossible
#print axioms drained_window_not_covered

end R1Step5Probe983b
end Dev
end Source
end ConnesWeilRH
