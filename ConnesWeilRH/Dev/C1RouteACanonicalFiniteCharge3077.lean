/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1RouteACanonicalOwner3076
import ConnesWeilRH.Dev.C1RouteAWeightedCellPartition2684
import ConnesWeilRH.Dev.C1RouteAWeightedPartitionSum2685
import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic

/-!
# Route A canonical finite-grid charge

Record 2800 covers the central cell only.  The full finite-grid price is the
exact 8192-cell ledger from record 2685.  This module exposes the four
per-channel cell-containment contracts and composes them with that ledger;
the cell contracts and the full-support tail remain explicit obligations.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open C1RouteAOwnerScaleAudit
open Source.C1RouteAItem5Arithmetic
open scoped BigOperators

noncomputable section

/-- Full 8192-cell ledger, reconstructed from every stored binary64 price as
an exact rational before casting to `Real`. -/
noncomputable def routeACanonicalFiniteGridCharge3077 : Real :=
  (((record2684CellTotalBits2685.map binary64Value2674).sum : ℚ) : Real)

theorem routeACanonicalFiniteGridCharge_eq_record2685_3077 :
    routeACanonicalFiniteGridCharge3077 =
      (((record2684CellTotalBits2685.map binary64Value2674).sum : ℚ) : Real) :=
  rfl

theorem routeACanonicalFiniteGridCharge_lt_knownError3077 :
    routeACanonicalFiniteGridCharge3077 < knownError2109 :=
  record2684GridChargeBelowKnownError2685

noncomputable def routeACanonicalBaseM0Function3077 : ℝ → ℂ :=
  externalPhysical2344 record2678BaseCoefficient capturedModulations2584

noncomputable def routeACanonicalBaseD2Function3077 : ℝ → ℂ :=
  deriv (deriv (correctedPhysical record2678BaseCoefficient
    capturedModulations2584))

noncomputable def routeACanonicalCorrectionM0Function3077 : ℝ → ℂ :=
  externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584

noncomputable def routeACanonicalCorrectionD2Function3077 : ℝ → ℂ :=
  deriv (deriv (correctedPhysical record2680CorrectionCoefficient
    capturedModulations2584))

/-- A single channel's continuum certificate over the shared 8192-cell grid.
Each field is cellwise: containment of the exact function in a complex
rectangle, a norm bound, a weight bound, interval integrability, and a price
for that cell. -/
structure CanonicalGridChannelCertificate3077
    (endpoint : ℕ → ℝ) (f : ℝ → ℂ) where
  rect : ℕ → ComplexRect2427
  normBound : ℕ → ℝ
  weightBound : ℕ → ℝ
  charge : ℕ → ℝ
  rectContains : ∀ k, k < 8192 → ∀ x ∈ Set.Icc (endpoint k) (endpoint (k + 1)),
    (rect k).Mem (f x)
  normBoundValid : ∀ k, k < 8192 → (rect k).cornerNorm ≤ normBound k
  weightBoundNonnegative : ∀ k, k < 8192 → 0 ≤ weightBound k
  weightBoundValid : ∀ k, k < 8192 → ∀ x ∈ Set.Icc (endpoint k) (endpoint (k + 1)),
    Real.exp ((-1 / 2 : ℝ) * x) ≤ weightBound k
  integrable : ∀ k, k < 8192 → IntervalIntegrable
    (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖)
    MeasureTheory.volume (endpoint k) (endpoint (k + 1))
  cellPrice : ∀ k, k < 8192 →
    (endpoint (k + 1) - endpoint k) *
      (weightBound k * normBound k) ≤ charge k

theorem canonicalGridChannelIntegral_le_chargeSum3077
    {endpoint : ℕ → ℝ} {f : ℝ → ℂ}
    (hendpoint : ∀ k, k < 8192 → endpoint k ≤ endpoint (k + 1))
    (certificate : CanonicalGridChannelCertificate3077 endpoint f) :
    (∫ x in (endpoint 0)..(endpoint 8192),
      Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖) ≤
      ∑ k ∈ Finset.range 8192, certificate.charge k := by
  exact weightedNormIntegral_le_of_partition2684
    (n := 8192) (endpoint := endpoint) (sigma := -1 / 2) (f := f)
    certificate.rect certificate.weightBound certificate.normBound certificate.charge
    hendpoint certificate.rectContains certificate.normBoundValid
    certificate.weightBoundNonnegative certificate.weightBoundValid
    certificate.integrable certificate.cellPrice

/-- The four channel certificates share one increasing partition. The last
field connects their separate prices to the exact total ledger from record
2685; matching only the cell count is insufficient. -/
structure CanonicalFourChannelGridCertificate3077 where
  endpoint : ℕ → ℝ
  endpointMonotone : ∀ k, k < 8192 → endpoint k ≤ endpoint (k + 1)
  baseM0 : CanonicalGridChannelCertificate3077 endpoint
    routeACanonicalBaseM0Function3077
  baseD2 : CanonicalGridChannelCertificate3077 endpoint
    routeACanonicalBaseD2Function3077
  correctionM0 : CanonicalGridChannelCertificate3077 endpoint
    routeACanonicalCorrectionM0Function3077
  correctionD2 : CanonicalGridChannelCertificate3077 endpoint
    routeACanonicalCorrectionD2Function3077
  ledgerBound :
    Finset.sum (Finset.range 8192) (fun k =>
      baseM0.charge k + baseD2.charge k +
        correctionM0.charge k + correctionD2.charge k) ≤
      routeACanonicalFiniteGridCharge3077

theorem canonicalFourChannelFiniteIntegral_le_gridCharge3077
    (grid : CanonicalFourChannelGridCertificate3077) :
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
          ‖routeACanonicalCorrectionD2Function3077 x‖) ≤
      routeACanonicalFiniteGridCharge3077 := by
  have h0 := canonicalGridChannelIntegral_le_chargeSum3077
    grid.endpointMonotone grid.baseM0
  have h1 := canonicalGridChannelIntegral_le_chargeSum3077
    grid.endpointMonotone grid.baseD2
  have h2 := canonicalGridChannelIntegral_le_chargeSum3077
    grid.endpointMonotone grid.correctionM0
  have h3 := canonicalGridChannelIntegral_le_chargeSum3077
    grid.endpointMonotone grid.correctionD2
  have hcharges :
      (∑ k ∈ Finset.range 8192, grid.baseM0.charge k) +
      (∑ k ∈ Finset.range 8192, grid.baseD2.charge k) +
      (∑ k ∈ Finset.range 8192, grid.correctionM0.charge k) +
      (∑ k ∈ Finset.range 8192, grid.correctionD2.charge k) ≤
      routeACanonicalFiniteGridCharge3077 := by
    have hsum := grid.ledgerBound
    let cells := Finset.range 8192
    have hdecomp :
        cells.sum grid.baseM0.charge +
        cells.sum grid.baseD2.charge +
        cells.sum grid.correctionM0.charge +
        cells.sum grid.correctionD2.charge =
        cells.sum (fun k => grid.baseM0.charge k + grid.baseD2.charge k +
          grid.correctionM0.charge k + grid.correctionD2.charge k) := by
      calc
        _ = (cells.sum grid.baseM0.charge + cells.sum grid.baseD2.charge) +
              (cells.sum grid.correctionM0.charge +
                cells.sum grid.correctionD2.charge) := by
          ring
        _ = cells.sum (fun k => grid.baseM0.charge k + grid.baseD2.charge k) +
              cells.sum (fun k => grid.correctionM0.charge k +
                grid.correctionD2.charge k) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        _ = cells.sum (fun k =>
              (grid.baseM0.charge k + grid.baseD2.charge k) +
                (grid.correctionM0.charge k + grid.correctionD2.charge k)) := by
          rw [← Finset.sum_add_distrib]
        _ = cells.sum (fun k => grid.baseM0.charge k + grid.baseD2.charge k +
              grid.correctionM0.charge k + grid.correctionD2.charge k) := by
          congr 1
          funext k
          ring
    rw [hdecomp]
    exact hsum
  linarith

/-- Add a separately proved tail and a signed-residual assembly inequality to
the full finite-grid enclosure. -/
theorem canonicalOwner_chargeRest_le_knownError_of_grid3077
    (grid : CanonicalFourChannelGridCertificate3077)
    {chargeRest tailCharge : ℝ}
    (hassembly : chargeRest ≤
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
            ‖routeACanonicalCorrectionD2Function3077 x‖) + tailCharge)
    (htail : tailCharge ≤
      knownError2109 - routeACanonicalFiniteGridCharge3077) :
    chargeRest ≤ knownError2109 := by
  have hfinite := canonicalFourChannelFiniteIntegral_le_gridCharge3077 grid
  linarith

end
end Dev
end ConnesWeilRH
