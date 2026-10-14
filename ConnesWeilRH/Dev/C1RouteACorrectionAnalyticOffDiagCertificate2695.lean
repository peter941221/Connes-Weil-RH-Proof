import ConnesWeilRH.Dev.C1RouteACorrectionAnalyticCertificate2601
import ConnesWeilRH.Dev.C1RouteAAnalyticContainmentBridge2646
import ConnesWeilRH.Dev.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.C1RouteAEntryManifest2664
import ConnesWeilRH.Dev.C1RouteACorrectionCandidateInverseMembership2600

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

/-! Concrete 2600 consumer: the candidate-inverse membership premise and all
50 manifest memberships are now discharged by imported proof-producing
assemblies.  Only the off-diagonal entries outside the 2664 manifest remain
as an explicit premise. -/

theorem capturedActualCorrectionOwner2584_realizes_of_remaining_offdiag_certificate2695_concrete
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (h_remaining : ∀ i j : Fin 30, i ≠ j →
      ¬ offdiagKnownInArtifacts2695 i j →
      (analyticMomentInterval2597 i j).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j))
    (hdefect_entry : ∀ i j : Fin 30,
      defectMatrix i j = matrixDefectEntry2598 candidateInverseMatrix2600
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584) i j)
    (hdefect_matrix :
      (ContinuousLinearMap.id ℂ (Fin 30 → ℂ)) -
          X.comp (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584) =
        matrixOperator2590 defectMatrix)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  apply capturedActualCorrectionOwner2584_realizes_of_remaining_offdiag_certificate2695
    X defectMatrix candidateInverseMatrix2600
      (fun i k => candidateInverseInterval2600_mem_candidateInverseMatrix2600 i k)
      ?_ h_remaining hdefect_entry hdefect_matrix row
  intro i j hparam
  exact parameterizedOffdiagManifest2664_mem i j hparam

end ConnesWeilRH.Dev
