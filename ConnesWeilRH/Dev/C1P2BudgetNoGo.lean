import ConnesWeilRH.Dev.C1P2DefectControl

/-!
# P2 scalar one-window budget no-go

The absolute-value one-window budget is incompatible with the live healthy
detector branch itself.  This leaf records that incompatibility for the full
`P2OneWindowBudgetWitness` contract, independently of the choice of reference
window.  It is a route guard, not an RH proof.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2BudgetNoGo

open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1OrbitWindowExitComposition
open C1P2DefectControl
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

/-- No healthy detector with strict negative `qw` can carry the scalar
one-window budget witness.  The witness consumer would produce the orbit gate
and hence `qw ≥ 0`, contradicting the detector's independently supplied
strictly negative spectral value. -/
theorem not_p2OneWindowBudgetWitness_of_healthyDetectorData
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (p : P2OneWindowBudgetWitness g) : False := by
  have hnegativeSpectral :
      C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0 :=
    (weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
      hdata.weilSquareSumPositive
  have hnegative : C1SameOwnerWeil.qw g < 0 := by
    rw [C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo]
    exact hnegativeSpectral
  have hnonnegative : 0 ≤ C1SameOwnerWeil.qw g :=
    qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate hdata
      (orbitGate_of_p2OneWindowBudgetWitness g p)
  exact (not_lt_of_ge hnonnegative) hnegative

end
end C1P2BudgetNoGo
end Source
end ConnesWeilRH
