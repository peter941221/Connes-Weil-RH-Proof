import ConnesWeilRH.Dev.WellFormHealthyRepoint
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData

/-!
# HealthyArchData — the data-bearing archimedean-term object the healthy SCAL/SCB reads

The lane-B `SourceScopedArchimedeanContributionBalance` (SCB) reads
`W.archimedeanTerm (W.convolutionStar f f)`.  To be a *data-bearing* owner
(AGENTS 6) rather than a placeholder, that value must be pinned to the real
CCM25 Eq.3.7 term via `totalArchimedean` on the healthy carrier.  This module
constructs the `SourceArchimedeanTermData` for `healthySymbols f` whose stored
`sourceArchimedeanTerm = totalArchimedean (healthyConvolutionStar f f)`,
and gives both read-offs (square-read-off and arch-read-off).

It does NOT prove the analytic SCAL balance; it supplies the data object the
balance is stated against.

RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace HealthyArchData

open WellFormHealthyRepoint
open CCM25Concrete.CompactArchTotal
open HealthySourceMellinAlgebra

/-- The healthy source symbols (over the full Schwartz carrier). -/
noncomputable abbrev healthySymbols := healthyWeilForm.toWeilFormSymbols

/-- `W.convolutionStar f f` on the healthy symbols is the true Mellin
   convolution square `healthyConvolutionStar f f`. -/
theorem healthySymbols_convolutionSquare_eq (f : TestFunction) :
    healthySymbols.convolutionStar f f = healthyConvolutionStar f f := by
  simp [healthySymbols, healthyWeilForm, healthyMellinSourceTestAlgebra,
    healthyLegacyTestEquiv, healthyConvolutionStar]

/-- The healthy archimedean term at the convolution square is exactly
   `totalArchimedean (healthyConvolutionStar f f)` (the real Eq.3.7 path). -/
theorem healthyArchData_readOff (f : TestFunction) :
    healthySymbols.archimedeanTerm
        (healthySymbols.convolutionStar f f) =
      totalArchimedean (healthyConvolutionStar f f) := by
  rw [healthySymbols_convolutionSquare_eq]
  exact WellFormHealthyRepoint.healthySymbols_archimedeanTerm_square f

/-- The data-bearing archimedean-term object for the healthy SCAL: it pins
   `sourceArchimedeanTerm` to `totalArchimedean (healthyConvolutionStar f f)`
   and proves both the square-read-off and the arch-read-off. -/
noncomputable def healthyArchData (f : TestFunction) :
    CCM25Concrete.FinitePrimeSourceData.SourceArchimedeanTermData healthySymbols f where
  sourceConvolutionSquare := healthyConvolutionStar f f
  sourceConvolutionSquareReadOff := healthySymbols_convolutionSquare_eq f
  sourceArchimedeanTerm := totalArchimedean (healthyConvolutionStar f f)
  archimedeanTermReadOff := by
    rw [← healthySymbols_convolutionSquare_eq f]
    exact healthyArchData_readOff f

end HealthyArchData
end Dev
end Source
end ConnesWeilRH