/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1RouteACanonicalFiniteCharge3077
import ConnesWeilRH.Dev.C1RouteAL1Enclosure

/-!
# Route A canonical selected-owner charge bridge

This consumer is fixed to the captured 2678/2680 canonical owner.  It no
longer accepts an arbitrary residual-family choice or a caller-supplied
`chargeRest <= record2686` hypothesis.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open scoped Interval
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1SpectralWeil
open ConnesWeilRH.Source.C1SpectralSummability
open ConnesWeilRH.Source.CC20YoshidaNearZeros
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable section

/-- Conditional certificate inputs for the canonical owner. The owner
identities are fixed by record 3076; `fullSupportAssembly` and `tailBudget`
remain explicit proof obligations and are not derived by this structure. -/
structure SelectedOwnerRepairedChargeBridge3073
    (grid : CanonicalFourChannelGridCertificate3077)
    (chargeRest tailCharge : Real) : Prop where
  sourceOwnerIdentity :
    routeACanonicalOwnerSource3076 = routeACanonicalOwner3076.sourceTest
  squareOwnerIdentity :
    routeACanonicalOwner3076.convolutionSquare =
      routeACanonicalOwner3076.sourceTest.convolutionSquare
  fullSupportAssembly :
    chargeRest ≤
      (∫ x in (grid.endpoint 0)..(grid.endpoint 8192),
          Real.exp ((-1 / 2 : ℝ) * x) *
            ‖routeACanonicalBaseM0Function3077 x‖) +
        (∫ x in (grid.endpoint 0)..(grid.endpoint 8192),
          Real.exp ((-1 / 2 : ℝ) * x) *
            ‖routeACanonicalBaseD2Function3077 x‖) +
        (∫ x in (grid.endpoint 0)..(grid.endpoint 8192),
          Real.exp ((-1 / 2 : ℝ) * x) *
            ‖routeACanonicalCorrectionM0Function3077 x‖) +
        (∫ x in (grid.endpoint 0)..(grid.endpoint 8192),
          Real.exp ((-1 / 2 : ℝ) * x) *
            ‖routeACanonicalCorrectionD2Function3077 x‖) + tailCharge
  tailBudget : tailCharge ≤
    Source.C1RouteAItem5Arithmetic.knownError2109 -
      routeACanonicalFiniteGridCharge3077

theorem selectedOwner_chargeRest_le_knownError_of_bridge3073
    {chargeRest tailCharge : Real}
    (grid : CanonicalFourChannelGridCertificate3077)
    (bridge : SelectedOwnerRepairedChargeBridge3073 grid chargeRest tailCharge) :
    chargeRest ≤ Source.C1RouteAItem5Arithmetic.knownError2109 := by
  exact canonicalOwner_chargeRest_le_knownError_of_grid3077 grid
    bridge.fullSupportAssembly bridge.tailBudget

/-- Canonical fixed-owner adapter into the existing certified item-5 producer.
The 101 strip-node bounds, certified L1 enclosure, gap split, four-channel
cell certificates, and full-support tail assembly remain explicit inputs. -/
theorem a005_item5_producer_wired_canonical_owner3073
    (grid : CanonicalFourChannelGridCertificate3077)
    (hnode : ∀ j : ℤ, -(50 : ℤ) ≤ j → j ≤ 50 →
      min (stripSecondNorm ((j : ℝ) / 100)
            (correctedPhysical record2678BaseCoefficient
              capturedModulations2584) *
           stripNorm ((j : ℝ) / 100)
            (correctedPhysical record2680CorrectionCoefficient
              capturedModulations2584))
          (stripSecondNorm ((j : ℝ) / 100)
            (correctedPhysical record2680CorrectionCoefficient
              capturedModulations2584) *
           stripNorm ((j : ℝ) / 100)
            (correctedPhysical record2678BaseCoefficient
              capturedModulations2584)) ≤ stripGridMax2303)
    {q gap chargeRest tailCharge windowCharge : ℝ}
    (hq : q ≤ l1UpperEnclosure2249)
    (bridge : SelectedOwnerRepairedChargeBridge3073 grid chargeRest tailCharge)
    (hsplit : gap ≤ windowCharge + tailCharge)
    (hwindow : windowCharge ≤ windowCharge2309)
    (htail : tailCharge ≤ tailCharge2307) :
    (∑' n : ℕ, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm
          (routeACanonicalBase3076.convolution routeACanonicalCorrection3076)
          rho.1) + chargeRest + gap + eps0FullTail2249 < -q := by
  simpa [routeACanonicalBase3076, routeACanonicalCorrection3076] using
    (a005_item5_producer_wired_owner_nodes_margin
      record2678BaseCoefficient record2680CorrectionCoefficient
      capturedModulations2584 hnode hq
      (selectedOwner_chargeRest_le_knownError_of_bridge3073 grid bridge)
      hsplit hwindow htail)

end
end Dev
end ConnesWeilRH
