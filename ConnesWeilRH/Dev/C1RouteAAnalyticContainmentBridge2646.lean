import ConnesWeilRH.Dev.C1RouteAOwnerDiagonalPartition2645
import ConnesWeilRH.Dev.C1RouteACorrectionAnalyticIntervals2597

namespace ConnesWeilRH.Dev

/-!
# Analytic containment bridge (record 2646)

The 2597 soundness socket asks for the full 30x30 containment
premise. The diagonal campaign (records 2634-2644, assembled in
record 2645) certifies the 30 diagonal entries. This bridge states
the exact remaining obligation shape: given the 870 off-diagonal
memberships, the full socket premise follows, with the diagonal
supplied by the certified partition theorem. The off-diagonal side
is the record-2624 GO-route campaign (pilot entry (0,3), complex
route at degree 55).
-/

/-- Socket discharge with the diagonal plugged in: the full 30x30
analytic containment follows from the off-diagonal memberships plus
the certified diagonal partition. -/
theorem socket_diagonal_split2646
    (h_offdiag : ∀ i j : Fin 30, i ≠ j →
      (analyticMomentInterval2597 i j).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j)) :
    ∀ i j : Fin 30,
      (analyticMomentInterval2597 i j).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j) := by
  intro i j
  rcases eq_or_ne i j with rfl | h
  · exact actualOwnerMomentMatrix2351_diagonal_mem2645 _
  · exact h_offdiag i j h

end ConnesWeilRH.Dev
