import ConnesWeilRH.Dev.L657DiagProbe

/-!
# R1 step 5b — `scopedArchimedeanContributionBalance` structurally refuted (983b)

The analytic leaf

    SourceScopedArchimedeanContributionBalance W f lambda gd rd

demands the equality of two scoped formulas:

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
| λ = 0 drain | ∅                         | 0      | 0 = Σ_g   (Σ_g > 0) ✗|
| λ = 2 full  | `{2}`                      | Σ_g    | Σ_g = Σ_g  ✓        |

The drained `λ = 0` case contradicts `globalSum_positive`, hence the whole
`∀λ` leaf is uninhabited on the concrete carrier — a **structural refutation**
(verdict 920 / L153), not missing analysis.  `L657DiagProbe.probe_balance_false`
already refutes the λ = 0 instance; this probe makes the structural form
explicit (`drained_forces_global_sum_zero`), so the `∀λ` verdict is explicit.

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

/-- On the concrete carrier the drained balance forces the global sum to
vanish — the refusal is direct. -/
theorem drained_forces_global_sum_zero :
    SourceScopedArchimedeanContributionBalance W0 f0 (0 : ℝ) gd rd →
    MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W0 f0 f0 gd = 0 := by
  intro hbal
  unfold SourceScopedArchimedeanContributionBalance at hbal
  simp only [SourceScopedRestrictedArchimedeanFormula,
             SourceScopedGlobalArchimedeanFormula,
             archimedeanTerm_zero, restrictedSumZero] at hbal
  rw [polePairingEqual] at hbal
  linarith

/-- The drained-window balance directly contradicts `globalSum_positive`. -/
theorem drained_balance_impossible :
    SourceScopedArchimedeanContributionBalance W0 f0 (0 : ℝ) gd rd → False := by
  intro hbal
  nlinarith [globalSum_positive, drained_forces_global_sum_zero hbal]

/-- The whole `∀λ` leaf is uninhabited on the concrete carrier. -/
theorem balance_family_refuted :
    ¬ (∀ lambda : ℝ,
        (rd : SourceRestrictedFinitePrimeArithmeticData W0 f0 f0 lambda) →
          SourceScopedArchimedeanContributionBalance W0 f0 lambda gd rd) := by
  intro hfam
  exact drained_balance_impossible (hfam 0 rd)

#print axioms drained_forces_global_sum_zero
#print axioms drained_balance_impossible
#print axioms balance_family_refuted

end R1Step5Probe983b
end Dev
end Source
end ConnesWeilRH