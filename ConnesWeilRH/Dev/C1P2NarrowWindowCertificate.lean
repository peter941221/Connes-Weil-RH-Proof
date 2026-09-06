import ConnesWeilRH.Dev.C1P2DefectControl
import ConnesWeilRH.Dev.C1LaneRStrictness

/-!
# P2 narrow reference-window certificate

The explicit narrow root is already known to have a strict negative
archimedean term and prime-free square support.  This leaf converts that
strict sign into the exact negative `ICgate` certificate consumed by the
same-owner P2 witness interfaces.  It supplies no detector comparison or
defect budget.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2NarrowWindowCertificate

open C1LaneRNarrowArch
open C1LaneRStrictness
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution

noncomputable section

theorem narrowArchRoot_ICgate_neg :
    ICgate narrowArchRoot.convolutionSquare < 0 := by
  unfold ICgate
  rw [finitePrimeSum_eq_zero_of_support_subset_open_log_two
    narrowArchRoot.convolutionSquare narrowArchRoot_square_support_subset_open_log_two]
  simpa using narrowArchRoot_archimedeanTerm_neg

theorem narrowArchRoot_exists_gate_certificate :
    ∃ μ : ℝ,
      0 < μ ∧ ICgate narrowArchRoot.convolutionSquare ≤ -μ := by
  refine ⟨-ICgate narrowArchRoot.convolutionSquare, ?_, ?_⟩
  · exact neg_pos.mpr narrowArchRoot_ICgate_neg
  · linarith

theorem narrowArchRoot_gate_certificate_of_margin
    {μ : ℝ}
    (hmargin : μ ≤ -ICgate narrowArchRoot.convolutionSquare) :
    ICgate narrowArchRoot.convolutionSquare ≤ -μ := by
  linarith

end
end C1P2NarrowWindowCertificate
end Source
end ConnesWeilRH
