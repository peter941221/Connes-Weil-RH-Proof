/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1C3CarrierTransport
import ConnesWeilRH.Dev.C1P2NarrowWindowCertificate

/-!
# Strict pinned C3' determinant margin

The existing carrier certificate records a nonpositive determinant.  The
explicit narrow root is in fact strictly negative, while a healthy detector
has a strictly positive pivot.  Their product therefore supplies an explicit
strict margin on the same carrier and owner; the cross channel is retained
with its exact square and is never estimated by an absolute majorant.
-/

namespace ConnesWeilRH
namespace Dev
namespace C1C3StrictPinnedMargin

open ConnesWeilRH.Source.C1P2NarrowWindowCertificate
open ConnesWeilRH.Source.C1LaneRNarrowArch
open ConnesWeilRH.Source.C1LocalConfigurationDomination
open ConnesWeilRH.Source.C1GateMatrixRepresentation
open C1C3CarrierTransport
open ConnesWeilRH.Source.C1HealthyYoshidaDetector
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.C1SameOwnerWeil
open Matrix
open scoped BigOperators

noncomputable section

noncomputable def carrierTwoSpanOptimalQform
    (γ : Real) (u v : CompactLogTest) : Real :=
  ((![1, -(
      ICgate ((carrierModulate γ u).involution.convolution
        (carrierModulate γ v)) /
        ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real) ⬝ᵥ
    (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
      (![1, -(
        ICgate ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) /
          ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real)))
  

theorem strict_carrier_twoSpan_determinant_margin_of_pinned_geometry
    {rho : ℂ} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (γ : Real) :
    ∃ μ : Real, 0 < μ ∧
      ICgate
          (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare *
          ICgate
            (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare -
        ICgate
          ((carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).involution.convolution
            (carrierModulate γ (carrierModulate (-γ) g))) ^ 2 ≤
      -μ := by
  have hu :
      ICgate
          (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare < 0 := by
    rw [carrierModulate_neg_inv γ narrowArchRoot]
    exact narrowArchRoot_ICgate_neg
  have hv :
      0 < ICgate
          (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare :=
    pinned_orbit_positive_pivot hdata γ
  refine ⟨(-ICgate narrowArchRoot.convolutionSquare) * ICgate g.convolutionSquare, ?_, ?_⟩
  · have hroot : 0 < -ICgate narrowArchRoot.convolutionSquare := by
      rw [← carrierModulate_neg_inv γ narrowArchRoot]
      exact neg_pos.mpr hu
    exact mul_pos hroot (by
      rw [← carrierModulate_neg_inv γ g]
      exact hv)
  · have hsq : 0 ≤
        ICgate
          ((carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).involution.convolution
            (carrierModulate γ (carrierModulate (-γ) g))) ^ 2 :=
      sq_nonneg _
    have hdet :
        ICgate
            (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare *
            ICgate
              (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare -
          ICgate
            ((carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).involution.convolution
              (carrierModulate γ (carrierModulate (-γ) g))) ^ 2 ≤
        ICgate
            (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare *
          ICgate
            (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare := by
      exact sub_le_self _ hsq
    calc
      _ ≤
          ICgate
              (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare *
            ICgate
              (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare := hdet
      _ = -((-ICgate narrowArchRoot.convolutionSquare) * ICgate g.convolutionSquare) := by
        rw [carrierModulate_neg_inv γ narrowArchRoot,
          carrierModulate_neg_inv γ g]
        ring

theorem strict_carrier_twoSpan_phase_budget_of_pinned_geometry
    {rho : ℂ} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (γ : Real) :
    ∃ μ : Real, 0 < μ ∧
      carrierArchimedeanDeterminantPhase γ
          (carrierModulate (-γ) narrowArchRoot)
          (carrierModulate (-γ) g) +
        carrierMixedDeterminantPhase γ
          (carrierModulate (-γ) narrowArchRoot)
          (carrierModulate (-γ) g) +
        carrierPrimeDeterminantPhase γ
          (carrierModulate (-γ) narrowArchRoot)
          (carrierModulate (-γ) g) ≤
      -μ := by
  obtain ⟨μ, hμ, hdet⟩ :=
    strict_carrier_twoSpan_determinant_margin_of_pinned_geometry hdata γ
  refine ⟨μ, hμ, ?_⟩
  rw [← carrier_twoSpan_determinant_split_phase]
  exact hdet

/- The existential margin above is useful to callers that only need a
   positive witness.  Keep the actual product visible as well: this is the
   quantitative form consumed by the optimal q-form below. -/
theorem strict_carrier_twoSpan_determinant_product_bound_of_pinned_geometry
    {rho : ℂ} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (γ : Real) :
    ICgate
        (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare *
        ICgate
          (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare -
      ICgate
        ((carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).involution.convolution
          (carrierModulate γ (carrierModulate (-γ) g))) ^ 2 ≤
      -((-ICgate narrowArchRoot.convolutionSquare) * ICgate g.convolutionSquare) := by
  have hu :
      ICgate
          (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare < 0 := by
    rw [carrierModulate_neg_inv γ narrowArchRoot]
    exact narrowArchRoot_ICgate_neg
  have hv :
      0 < ICgate
          (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare :=
    pinned_orbit_positive_pivot hdata γ
  have hsq : 0 ≤
      ICgate
        ((carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).involution.convolution
          (carrierModulate γ (carrierModulate (-γ) g))) ^ 2 :=
    sq_nonneg _
  have hdet :
      ICgate
          (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare *
          ICgate
            (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare -
        ICgate
          ((carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).involution.convolution
            (carrierModulate γ (carrierModulate (-γ) g))) ^ 2 ≤
      ICgate
          (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare *
        ICgate
          (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare := by
    exact sub_le_self _ hsq
  calc
    _ ≤ ICgate
          (carrierModulate γ (carrierModulate (-γ) narrowArchRoot)).convolutionSquare *
        ICgate
          (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare := hdet
    _ = -((-ICgate narrowArchRoot.convolutionSquare) * ICgate g.convolutionSquare) := by
      rw [carrierModulate_neg_inv γ narrowArchRoot,
        carrierModulate_neg_inv γ g]
      ring

theorem strict_carrier_twoSpan_optimal_qform_margin_of_pinned_geometry
    {rho : ℂ} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (γ : Real) :
    ∃ μ : Real, 0 < μ ∧
      carrierTwoSpanOptimalQform γ
        (carrierModulate (-γ) narrowArchRoot)
        (carrierModulate (-γ) g) ≤ -μ := by
  have hB :
      0 < ICgate (carrierModulate γ (carrierModulate (-γ) g)).convolutionSquare :=
    pinned_orbit_positive_pivot hdata γ
  have hdet := strict_carrier_twoSpan_determinant_product_bound_of_pinned_geometry
    hdata γ
  refine ⟨-ICgate narrowArchRoot.convolutionSquare,
    neg_pos.mpr narrowArchRoot_ICgate_neg, ?_⟩
  rw [carrierTwoSpanOptimalQform,
    carrier_twoSpan_gate_qform_at_optimal_lambda γ
    (carrierModulate (-γ) narrowArchRoot) (carrierModulate (-γ) g) hB]
  apply (div_le_iff₀ hB).2
  have hdet' := hdet
  rw [carrierModulate_neg_inv γ narrowArchRoot,
    carrierModulate_neg_inv γ g] at hdet' ⊢
  nlinarith [hdet']

end
end C1C3StrictPinnedMargin
end Dev
end ConnesWeilRH
