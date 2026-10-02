import ConnesWeilRH.Dev.C1RouteAExternalOwnerIdentity
import ConnesWeilRH.Dev.C1RouteAMPFRInterface

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem correctedPhysical_mem_of_family_rect2436
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (position : ℝ) (rect : Fin 30 → ComplexRect2427)
    (hterm : ∀ index : Fin 30,
      (rect index).Mem (externalFamilyValue2344 (coefficients index)
        (modulations index) (storedWidth index ^ 2) position)) :
    (ComplexRect2427.sumFinset rect Finset.univ).Mem
      (correctedPhysical coefficients modulations position) := by
  rw [← externalPhysical2344_eq_correctedPhysical coefficients modulations]
  unfold externalPhysical2344
  apply ComplexRect2427.mem_sumFinset
  intro index hindex
  exact hterm index

theorem externalFamilyValue_mem_of_factor_cert2437
    (coefficient bump phase : DirectedComplexValue2433)
    (target : ℂ)
    (hvalue : ((coefficient.product bump).product phase).value = target) :
    ((coefficient.product bump).product phase).rectangle.Mem target := by
  rw [← hvalue]
  exact ((coefficient.product bump).product phase).contains

end ConnesWeilRH.Dev
