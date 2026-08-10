import ConnesWeilRH.Dev.ScabNormalForm
import ConnesWeilRH.Dev.ScabHealthyTarget
import ConnesWeilRH.Dev.HealthyArchData

/-!
# ScabLhsZero - the SCAL left hand side is structurally zero

The SCAL scalar target (docs/952) is

    poleFunctional(convolution f) - polePairing(f)
        = 2*archimedeanTerm(convolution f) + (global - restricted)

Because `polePairing(f) = poleFunctional(convolutionSquare f)` and on the
healthy carrier `convolutionSquare = convolutionStar`, the whole left side
cancels to 0.  Therefore Wall-A 1.4 reduces to the single arch/prime-difference
relation

    2*archimedeanTerm(convolution f) + (global - restricted) = 0

This module proves the structural reduction (the LHS-zero identity) and the
equivalence of the target with the arch/prime relation.  It does NOT prove the
analytic arch identity itself (open).  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace ScabLhsZero

open WellFormHealthyRepoint
open ConnesWeilRH.Source.CCM25Concrete.ScabNormalForm

/-- The healthy carrier symbols. -/
noncomputable abbrev healthySymbols : WeilFormSymbols :=
  WellFormHealthyRepoint.healthyWeilForm.toWeilFormSymbols

/-- polePairing(f) = poleFunctional(convolution f) on the healthy carrier. -/
theorem polePairing_eq_polarSquare (f : TestFunction) :
    healthySymbols.polePairing f =
      healthySymbols.poleFunctional (healthySymbols.convolutionStar f f) := by
  unfold healthySymbols
  simp
  rfl

/-- The SCAL left side cancels identically (structural - no arch/prime content). -/
theorem lhs_zero (f : TestFunction) :
    healthySymbols.poleFunctional (healthySymbols.convolutionStar f f) -
        healthySymbols.polePairing f = 0 := by
  rw [polePairing_eq_polarSquare f]
  ring

/-- The Wall-A 1.4 target is equivalent to the arch/prime-difference relation
   2*arch + (a-b) = 0 (the only live content after the LHS cancels). -/
theorem scab_target_iff_arch_prime
    (f : TestFunction) (a b : Real) :
      ScabPoleArchTarget healthySymbols f a b <->
        2 * (HealthyArchData.healthyArchData f).sourceArchimedeanTerm + (a - b) = 0 := by
  have hz : healthySymbols.poleFunctional (healthySymbols.convolutionStar f f) -
        healthySymbols.polePairing f = 0 := lhs_zero f
  constructor <;> intro h
  · unfold ScabPoleArchTarget at h
    rw [ConnesWeilRH.Source.Dev.ScabHealthyTarget.healthyArch_readOff f] at h
    linarith
  · unfold ScabPoleArchTarget
    rw [ConnesWeilRH.Source.Dev.ScabHealthyTarget.healthyArch_readOff f]
    linarith

end ScabLhsZero
end Dev
end Source
end ConnesWeilRH