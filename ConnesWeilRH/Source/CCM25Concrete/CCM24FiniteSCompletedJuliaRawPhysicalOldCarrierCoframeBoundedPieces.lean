/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger

/-!
# Exact bookkeeping split for the old-carrier coframe row

This owner exposes the small algebraic split used by the coframe
divide-and-conquer package.  Norm estimates deliberately live in the
lower-level response owner; this file does not turn them into a readout.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope

noncomputable def suffixActualBandRawPhysicalOldCarrierKnownBoundedRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  suffixActualBandRawPhysicalOldCarrierMetricInclusionRow owner lambda p S +
    suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
      owner lambda p S

noncomputable def suffixActualBandRawPhysicalOldCarrierHardRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  suffixActualBandRawPhysicalOldCarrierMetricOrientationRow owner lambda p S +
    suffixActualBandRawPhysicalOldCarrierMetricResidualRow owner lambda p S

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_hard_add_known
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierHardRow owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierKnownBoundedRow owner lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_orientation_add_residual_add_forwardComplete,
    suffixActualBandRawPhysicalOldCarrierHardRow,
    suffixActualBandRawPhysicalOldCarrierKnownBoundedRow]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.add_apply]
  abel

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
end CCM25Concrete
end Source
end ConnesWeilRH
