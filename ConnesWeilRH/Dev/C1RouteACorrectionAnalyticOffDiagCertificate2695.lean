import ConnesWeilRH.Dev.C1RouteACorrectionAnalyticCertificate2601
import ConnesWeilRH.Dev.C1RouteAAnalyticContainmentBridge2646
import ConnesWeilRH.Dev.C1RouteAEntryAssembly2663

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

/-! Off-diagonal interface for the integrated analytic certificate.

The diagonal entries are already certified by record 2645.  This bridge
plugs that result into record 2601 so callers only carry the genuinely open
off-diagonal containment premise instead of repeating the full 30 by 30
matrix premise.
-/

theorem capturedActualCorrectionOwner2584_realizes_of_offdiag_analytic_interval_certificate2695
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (x : Matrix (Fin 30) (Fin 30) ℂ)
    (hx : ∀ i k : Fin 30,
      (candidateInverseInterval2600 i k).Mem (x i k))
    (h_offdiag : ∀ i j : Fin 30, i ≠ j →
      (analyticMomentInterval2597 i j).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j))
    (hdefect_entry : ∀ i j : Fin 30,
      defectMatrix i j = matrixDefectEntry2598 x
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584) i j)
    (hdefect_matrix :
      (ContinuousLinearMap.id ℂ (Fin 30 → ℂ)) -
          X.comp (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584) =
        matrixOperator2590 defectMatrix)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  exact capturedActualCorrectionOwner2584_realizes_of_analytic_interval_certificate2601
    X defectMatrix x hx (socket_diagonal_split2646 h_offdiag)
    hdefect_entry hdefect_matrix row

/-! The 2664 manifest records 49 reproducible entry chains, but their generated
Lean sources are not imported here. A caller must still provide those 49
memberships through `h_manifest`. The earlier hand-written assembly does close
`(0,3)` directly, so this split reduces the formal pointwise premise count from
870 to 869; it only separates the manifest-listed entries from the rest. -/

def parameterizedOffdiagManifest2664 (i j : Fin 30) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 4) ∨
  (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨
  (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
  (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 4) ∨
  (i = 4 ∧ j = 0) ∨ (i = 4 ∧ j = 1) ∨ (i = 4 ∧ j = 3) ∨
  (i = 5 ∧ j = 6) ∨ (i = 5 ∧ j = 7) ∨
  (i = 6 ∧ j = 5) ∨ (i = 6 ∧ j = 7) ∨
  (i = 7 ∧ j = 5) ∨ (i = 7 ∧ j = 6) ∨
  (i = 13 ∧ j = 3) ∨
  (i = 14 ∧ j = 3) ∨ (i = 15 ∧ j = 3) ∨ (i = 16 ∧ j = 3) ∨
  (i = 17 ∧ j = 3) ∨ (i = 18 ∧ j = 3) ∨
  (i = 19 ∧ j = 2) ∨ (i = 19 ∧ j = 3) ∨
  (i = 20 ∧ j = 2) ∨ (i = 20 ∧ j = 3) ∨
  (i = 21 ∧ j = 2) ∨ (i = 21 ∧ j = 3) ∨
  (i = 22 ∧ j = 2) ∨ (i = 22 ∧ j = 3) ∨
  (i = 23 ∧ j = 2) ∨ (i = 23 ∧ j = 3) ∨
  (i = 24 ∧ j = 2) ∨ (i = 24 ∧ j = 3) ∨
  (i = 25 ∧ j = 2) ∨ (i = 25 ∧ j = 3) ∨
  (i = 26 ∧ j = 2) ∨ (i = 26 ∧ j = 3) ∨
  (i = 27 ∧ j = 2) ∨ (i = 27 ∧ j = 3) ∨ (i = 27 ∧ j = 7) ∨
  (i = 28 ∧ j = 2) ∨ (i = 28 ∧ j = 3) ∨ (i = 28 ∧ j = 7) ∨
  (i = 29 ∧ j = 2) ∨ (i = 29 ∧ j = 3) ∨ (i = 29 ∧ j = 7)

def offdiagKnownInArtifacts2695 (i j : Fin 30) : Prop :=
  (i = 0 ∧ j = 3) ∨ parameterizedOffdiagManifest2664 i j

theorem capturedActualCorrectionOwner2584_realizes_of_remaining_offdiag_certificate2695
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (x : Matrix (Fin 30) (Fin 30) ℂ)
    (hx : ∀ i k : Fin 30,
      (candidateInverseInterval2600 i k).Mem (x i k))
    (h_manifest : ∀ i j : Fin 30, parameterizedOffdiagManifest2664 i j →
      (analyticMomentInterval2597 i j).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j))
    (h_remaining : ∀ i j : Fin 30, i ≠ j →
      ¬ offdiagKnownInArtifacts2695 i j →
      (analyticMomentInterval2597 i j).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j))
    (hdefect_entry : ∀ i j : Fin 30,
      defectMatrix i j = matrixDefectEntry2598 x
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584) i j)
    (hdefect_matrix :
      (ContinuousLinearMap.id ℂ (Fin 30 → ℂ)) -
          X.comp (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584) =
        matrixOperator2590 defectMatrix)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  apply capturedActualCorrectionOwner2584_realizes_of_offdiag_analytic_interval_certificate2695
    X defectMatrix x hx ?_ hdefect_entry hdefect_matrix row
  intro i j hne
  by_cases hknown : offdiagKnownInArtifacts2695 i j
  · rcases hknown with h03 | hparam
    · obtain ⟨rfl, rfl⟩ := h03
      exact entry03Mem2663
    · exact h_manifest i j hparam
  · exact h_remaining i j hne hknown

end ConnesWeilRH.Dev
