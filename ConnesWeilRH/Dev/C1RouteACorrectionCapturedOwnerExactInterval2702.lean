import ConnesWeilRH.Dev.C1RouteACorrectionExactIntervals2586
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureOwner2584

namespace ConnesWeilRH.Dev

/-! Live-owner consumer for the exact 2338 interval interface. The analytic
soundness premise remains explicit; this theorem only performs the named
interval-to-box transfer for the owner used by the route. -/
theorem capturedActualCorrectionOwner2584_mem_of_exactInterval2702
    (h_exact_interval : ∀ i : Fin 30,
      (exactCorrectionInterval2586 i).Mem
        (capturedActualCorrectionOwner2584 i)) :
    ∀ i : Fin 30,
      (correctionCoefficientBox2570 i).Mem
        (capturedActualCorrectionOwner2584 i) := by
  exact actualCorrectionOwner_mem_correctionBox_of_exactInterval2586
    capturedActualCorrectionOwner2584 h_exact_interval

end ConnesWeilRH.Dev
