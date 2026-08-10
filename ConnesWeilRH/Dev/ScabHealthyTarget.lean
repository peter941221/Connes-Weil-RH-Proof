import ConnesWeilRH.Dev.ScabNormalForm
import ConnesWeilRH.Dev.HealthyArchData

/-!
# ScabHealthyTarget - the named, data-bearing scalar target of the healthy SCB

SourceScopedArchimedeanContributionBalance is false on concreteWeilForm
(concrete archimedeanTerm = 0, cf. L657DiagProbe.probe_balance_false).  The
only living statement is the healthy-carrier SCB, whose arch slot is the true
CCM25 Eq.3.7 term via totalArchimedean (WellFormHealthyRepoint re-point +
HealthyArchData).

This module (1) pins the healthy arch read-off to totalArchimedean via the
data-bearing HealthyArchData.healthyArchData, and (2) reduces the SCB pair
equality to the single named scalar target ScabPoleArchTarget, the exact
pole/pole + arch identity a Wall-A 1.4 analytic proof must show.  It does
NOT prove that identity; the analytic argument is the open bottom.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace ScabHealthyTarget

open WellFormHealthyRepoint
open CCM25Concrete.ScabNormalForm

/-- The healthy carrier symbols (healthyWeilForm.toWeilFormSymbols). -/
noncomputable abbrev healthySymbols := HealthyArchData.healthySymbols

/-- The data-bearing archimedean term at the convolution square is the true
   CCM Eq.3.7 term via totalArchimedean. -/
theorem healthyArch_readOff (f : TestFunction) :
    healthySymbols.archimedeanTerm (healthySymbols.convolutionStar f f) =
      (HealthyArchData.healthyArchData f).sourceArchimedeanTerm := by
  rw [HealthyArchData.healthyArchData_readOff f]
  rfl

/-- The healthy reduced-balance pair equality is *equivalent* to the single
   scalar pole/arch target (pure ring identity, via ScabNormalForm). -/
theorem scb_iff_arch_target
    (f : TestFunction) (a b : Real) :
    (healthySymbols.archimedeanTerm (healthySymbols.convolutionStar f f)
          + healthySymbols.polePairing f - b =
     healthySymbols.poleFunctional (healthySymbols.convolutionStar f f)
          - healthySymbols.archimedeanTerm (healthySymbols.convolutionStar f f)
          - a) <-> ScabPoleArchTarget healthySymbols f a b := by
  exact scab_iff_pole_arch_target healthySymbols f a b

end ScabHealthyTarget
end Dev
end Source
end ConnesWeilRH
