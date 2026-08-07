import Mathlib.Analysis.InnerProductSpace.PiL2
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FiniteCarrierGateInstance

open scoped ComplexConjugate InnerProduct
open ConnesWeilRH.Source.CC20Concrete.PositiveTrace

abbrev FinCarrier : Type := EuclideanSpace ℂ (Fin 2)

/-- The standard orthonormal Hilbert basis of the 2-dim finite carrier.  Its
index type is Fin (finrank ℂ FinCarrier), which is a Fin hence Fintype. -/
noncomputable def carrierBasis :
    HilbertBasis (Fin (Module.finrank ℂ FinCarrier)) ℂ FinCarrier :=
  (stdOrthonormalBasis ℂ FinCarrier).toHilbertBasis

/-- Non-vacuous finite Gate instance: on the 2-dim HS carrier, the identity
operator's real-part trace is bounded by card * ||1|| = finrank * 1, which
the route-A machine actually proves. -/
theorem id_finite_gate_instance :
    ‖(ordinaryTraceAlong carrierBasis (1 : FinCarrier →L[ℂ] FinCarrier)).re‖ ≤
      (Module.finrank ℂ FinCarrier : ℝ) * ‖(1 : FinCarrier →L[ℂ] FinCarrier)‖ := by
  simpa [Fintype.card_fin] using
    (abs_re_ordinaryTraceAlong_le_card_mul_opNorm carrierBasis
      (1 : FinCarrier →L[ℂ] FinCarrier))

end FiniteCarrierGateInstance
end CCM25Concrete
end Source
end ConnesWeilRH
