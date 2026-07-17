/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ProlateTraceReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

/-!
# Unit-scale prolate trace reduction

This module applies the generic two-projection defect theorem to the literal
CC20 source cutoff.  It reduces the missing positive trace-class theorem to
two source-specific facts about one actual operator:

1. the raw Hardy--Titchmarsh half-line crossing is Hilbert--Schmidt;
2. the complementary support angle is strict.

Neither fact is assumed globally or packaged as stored spectral data.  They
remain explicit premises until constructed from the CC20 unit-scale source.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24UnitScaleProlateTraceReduction

open CC20Concrete
open CC20Concrete.ProlateTraceReduction
open CC20Concrete.PositiveTrace
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace
open CCM24UnitScaleProlateAlignment

local notation "Hinf" => ccm24ArchimedeanHardyTitchmarsh
local notation "H" => finiteSCarrier

noncomputable abbrev unitProlateFactor : H →L[ℂ] H :=
  prolateFactor Hinf

noncomputable abbrev unitProlateDefectFactor : H →L[ℂ] H :=
  prolateDefectFactor Hinf

noncomputable abbrev unitRawSupportCrossing : H →L[ℂ] H :=
  (ContinuousLinearMap.id ℂ H - cc20PositiveHalfLineProjection) ∘L
    cc20TransportedHalfLineProjection Hinf ∘L
      cc20PositiveHalfLineProjection

theorem unitProlateFactor_eq_source :
    unitProlateFactor =
      sourceProlateHilbertSchmidtFactor unitSoninScale := by
  unfold unitProlateFactor prolateFactor supportComplementProjection
    sourceProlateHilbertSchmidtFactor
  rw [radialSupportProjection_unit,
    sourceFourierSupportProjection_unit,
    sourceSoninProjection_unit]

theorem unitProlateDefectFactor_eq_rawSupportCrossing :
    unitProlateDefectFactor = unitRawSupportCrossing :=
  prolateDefectFactor_eq_rawSupportCrossing Hinf

/-- The exact unit-scale positive trace-class producer once the two genuine
CC20 analytic facts are supplied.  This theorem adds no spectral premise to
the project state: both obligations remain visible at the call site. -/
theorem sourceProlateRemainder_unit_isTraceClassAlong_of_rawCrossing
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (hangle : ‖unitProlateFactor‖ < 1)
    (hcrossing : Summable fun i =>
      ‖unitRawSupportCrossing (basis i)‖ ^ 2) :
    IsTraceClassAlong basis
      (sourceProlateRemainder unitSoninScale) := by
  have hdefect : Summable fun i =>
      ‖unitProlateDefectFactor (basis i)‖ ^ 2 := by
    simpa only [unitProlateDefectFactor_eq_rawSupportCrossing] using hcrossing
  rw [sourceProlateRemainder_unit]
  exact prolateRemainder_isTraceClassAlong_of_strictAngle basis Hinf
    hangle hdefect

/-- The same reduction in the Hilbert--Schmidt factor shape consumed by the
fixed-source three-branch ledger. -/
theorem sourceProlateHilbertSchmidtFactor_unit_summable_of_rawCrossing
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (hangle : ‖unitProlateFactor‖ < 1)
    (hcrossing : Summable fun i =>
      ‖unitRawSupportCrossing (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor unitSoninScale (basis i)‖ ^ 2 := by
  rw [← unitProlateFactor_eq_source]
  exact prolateFactor_summable_of_strictAngle basis Hinf hangle
    (by simpa only [unitProlateDefectFactor_eq_rawSupportCrossing] using
      hcrossing)

end CCM24UnitScaleProlateTraceReduction
end CCM25Concrete
end Source
end ConnesWeilRH
