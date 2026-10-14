import ConnesWeilRH.Dev.C1RouteACorrectionExactIntervals2586
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureOwner2584
import ConnesWeilRH.Dev.C1RouteACorrectionInvariantBox2696

namespace ConnesWeilRH.Dev

open Function

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

/-! The fixed-point consumer uses the actual owner as the fixed point of the
contracting coefficient map.  The three analytic obligations are kept
explicit: completeness of the concrete coefficient box, forward invariance
of the map, and the finite initial displacement required by Mathlib's
contracting-map theorem. -/

def correctionCoefficientBoxSet2570 : Set (Fin 30 → ℂ) :=
  Set.pi Set.univ (fun i : Fin 30 =>
    {z : ℂ | (correctionCoefficientBox2570 i).Mem z})

theorem correctionCoefficientBoxSet2570_isClosed :
    IsClosed correctionCoefficientBoxSet2570 := by
  apply isClosed_set_pi
  intro i hi
  have hreLo : IsClosed {z : ℂ |
      (correctionCoefficientBox2570 i).reLo ≤ z.re} :=
    isClosed_Ici.preimage Complex.continuous_re
  have hreHi : IsClosed {z : ℂ |
      z.re ≤ (correctionCoefficientBox2570 i).reHi} :=
    isClosed_Iic.preimage Complex.continuous_re
  have himLo : IsClosed {z : ℂ |
      (correctionCoefficientBox2570 i).imLo ≤ z.im} :=
    isClosed_Ici.preimage Complex.continuous_im
  have himHi : IsClosed {z : ℂ |
      z.im ≤ (correctionCoefficientBox2570 i).imHi} :=
    isClosed_Iic.preimage Complex.continuous_im
  change IsClosed ({z : ℂ |
    (correctionCoefficientBox2570 i).reLo ≤ z.re} ∩
      ({z : ℂ | z.re ≤ (correctionCoefficientBox2570 i).reHi} ∩
        ({z : ℂ | (correctionCoefficientBox2570 i).imLo ≤ z.im} ∩
          {z : ℂ | z.im ≤ (correctionCoefficientBox2570 i).imHi})))
  exact hreLo.inter (hreHi.inter (himLo.inter himHi))

theorem correctionCoefficientCenter_mem_boxSet2570 :
    correctionCoefficientBoxSet2570 correctionCoefficientCenter2570 := by
  change ∀ i ∈ Set.univ,
    (correctionCoefficientBox2570 i).Mem (correctionCoefficientCenter2570 i)
  intro i hi
  exact corrCenter_mem2570 i

theorem capturedActualCorrectionOwner2584_mem_of_fixedPoint_invariant_box2696
    {K : NNReal}
    {f : (Fin 30 → ℂ) → (Fin 30 → ℂ)}
    (hf : ContractingWith K f)
    (hcomplete : IsComplete correctionCoefficientBoxSet2570)
    (hinvariant : Set.MapsTo f correctionCoefficientBoxSet2570
      correctionCoefficientBoxSet2570)
    (hfinite : Ne
      (edist correctionCoefficientCenter2570
        (f correctionCoefficientCenter2570)) ⊤)
    (hfixed : IsFixedPt f capturedActualCorrectionOwner2584) :
    ∀ i : Fin 30,
      (correctionCoefficientBox2570 i).Mem
        (capturedActualCorrectionOwner2584 i) := by
  have hmem : correctionCoefficientBoxSet2570
      capturedActualCorrectionOwner2584 :=
    fixedPoint_mem_of_complete_invariant_set2696 hf hcomplete hinvariant
      correctionCoefficientCenter_mem_boxSet2570 hfinite hfixed
  change ∀ i ∈ Set.univ,
    (correctionCoefficientBox2570 i).Mem
      (capturedActualCorrectionOwner2584 i) at hmem
  exact fun i => hmem i (Set.mem_univ i)

end ConnesWeilRH.Dev
