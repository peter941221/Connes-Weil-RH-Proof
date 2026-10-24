/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1RouteAExternalOwnerIdentity
import ConnesWeilRH.Dev.C1RouteAOwnerNodes
import ConnesWeilRH.Dev.C1RouteASelectedOwnerSupport
import ConnesWeilRH.Dev.C1ChargeRestRecord2686Identity2800

/-!
# Route A canonical captured owner

This module fixes the coefficient and modulation owner used by records
2678/2680.  It does not quantify over the arbitrary residual-correction
family.  The exact representation lemmas below are the owner identity needed
before any finite-window charge can be consumed.
-/

namespace ConnesWeilRH
namespace Dev

open ConnesWeilRH.Source
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open ConnesWeilRH.Source.C1RouteASelectedOwnerSupport
open C1RouteAOwnerScaleAudit

noncomputable section

noncomputable def routeACanonicalBase3076 : CompactLogTest :=
  correctedPhysicalCompactLogTest record2678BaseCoefficient
    capturedModulations2584

noncomputable def routeACanonicalCorrection3076 : CompactLogTest :=
  correctedPhysicalCompactLogTest record2680CorrectionCoefficient
    capturedModulations2584

noncomputable def routeACanonicalOwnerSource3076 : CompactLogTest :=
  halfDensityShift
    (routeACanonicalBase3076.convolution routeACanonicalCorrection3076)

noncomputable def routeACanonicalOwner3076 :
    ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner :=
  selectedOwner routeACanonicalBase3076 routeACanonicalCorrection3076 0

theorem routeACanonicalBase_test_eq_external3076 :
    (routeACanonicalBase3076.test : ℝ → ℂ) =
      externalPhysical2344 record2678BaseCoefficient
        capturedModulations2584 := by
  simpa [routeACanonicalBase3076] using
    (externalPhysical2344_eq_correctedPhysical
      record2678BaseCoefficient capturedModulations2584).symm

theorem routeACanonicalCorrection_test_eq_external3076 :
    (routeACanonicalCorrection3076.test : ℝ → ℂ) =
      externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 := by
  simpa [routeACanonicalCorrection3076] using
    (externalPhysical2344_eq_correctedPhysical
      record2680CorrectionCoefficient capturedModulations2584).symm

theorem routeACanonicalBase_support3076 :
    Function.support routeACanonicalBase3076.test ⊆
      Set.Ioo (-stripRadius2303) stripRadius2303 := by
  exact capturedFactor_support_open_pin
    record2678BaseCoefficient capturedModulations2584

theorem routeACanonicalCorrection_support3076 :
    Function.support routeACanonicalCorrection3076.test ⊆
      Set.Ioo (-stripRadius2303) stripRadius2303 := by
  exact capturedFactor_support_open_pin
    record2680CorrectionCoefficient capturedModulations2584

theorem routeACanonicalOwnerSource_eq3076 :
    routeACanonicalOwnerSource3076 =
      (routeACanonicalOwner3076).sourceTest := by
  rfl

theorem routeACanonicalOwnerSource_support3076 :
    Function.support routeACanonicalOwnerSource3076.test ⊆
      Set.Ioo
        (-(((0 + 1 : Nat) : Real) * stripRadius2303 + stripRadius2303))
        (((0 + 1 : Nat) : Real) * stripRadius2303 + stripRadius2303) := by
  rw [routeACanonicalOwnerSource_eq3076]
  have hsource := selectedOwner_source_support_composed
    routeACanonicalBase3076 routeACanonicalCorrection3076 0
    (by
      simpa only [routeACanonicalBase3076] using
        (capturedFactor_support_open_pin
          record2678BaseCoefficient capturedModulations2584))
    (by
      simpa only [routeACanonicalCorrection3076] using
        (capturedFactor_support_open_pin
          record2680CorrectionCoefficient capturedModulations2584))
  exact hsource

theorem routeARecordedCenterCellChannelCharge_eq_record2800_terms3076 :
    (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2678BaseCoefficient
            capturedModulations2584 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖deriv (deriv (correctedPhysical record2678BaseCoefficient
            capturedModulations2584)) x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2680CorrectionCoefficient
            capturedModulations2584 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖deriv (deriv (correctedPhysical record2680CorrectionCoefficient
            capturedModulations2584)) x‖) =
      record2686RepairedOwnerTotal2800 := by
  rfl

end
end Dev
end ConnesWeilRH
