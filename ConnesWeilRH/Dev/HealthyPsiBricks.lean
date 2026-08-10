import ConnesWeilRH.Dev.WellFormHealthyRepoint
import ConnesWeilRH.Basic

/-!
# HealthyPsiSignature — psi/qw identity closure on the healthy carrier

The lane-B Wall-A statement set (SCB / QW / psi) is only meaningful if the carrier's
`psi`, `qw` are the *real* explicit-formula objects, not placeholders.  On the healthy
carrier `SourceWeilFormData.psi` is defined as

    poleFunctional F - archimedeanTerm F - sum_{global primes} finitePrimeTerm n F

and `qw` is its self-convolution, so `PsiSignStatement` and `QWDefinitionStatement`
hold by definitional unfolding.  This module closes that data objection for Wall-A.  It
does NOT prove the analytic scalar balance itself (Wall-A 1.4 stays open).  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace HealthyPsiBricks

open WellFormHealthyRepoint
open ConnesWeilRH.WeilFormSymbols

/-- The healthy carrier symbols (`healthyWeilForm.toWeilFormSymbols`). -/
noncomputable abbrev healthySymbols : WeilFormSymbols :=
  WellFormHealthyRepoint.healthyWeilForm.toWeilFormSymbols

/-- The healthy `psi` is exactly the pole/arch/global-prime explicit-formula
   composite (definitional; closes by unfolding). -/
theorem healthyPsi_sign :
    ConnesWeilRH.WeilFormSymbols.PsiSignStatement healthySymbols := by
  unfold ConnesWeilRH.WeilFormSymbols.PsiSignStatement
  intro F
  simp [healthySymbols]
  unfold ConnesWeilRH.Source.AnalyticCore.SourceWeilFormData.psi
  simp

/-- The healthy `qw` is definitionally the self-convolution of the real psi. -/
theorem healthyQWDef :
    ConnesWeilRH.WeilFormSymbols.QWDefinitionStatement healthySymbols := by
  unfold ConnesWeilRH.WeilFormSymbols.QWDefinitionStatement
  intro f g
  simp [healthySymbols,
        ConnesWeilRH.Source.AnalyticCore.SourceWeilFormData.qw,
        ConnesWeilRH.Source.AnalyticCore.SourceWeilFormData.psi]

end HealthyPsiBricks
end Dev
end Source
end ConnesWeilRH