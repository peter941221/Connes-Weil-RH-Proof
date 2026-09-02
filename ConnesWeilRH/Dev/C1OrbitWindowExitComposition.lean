/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# C1: the C3 exit composition (record 1099)

Record 1089 pinned the orbit detector (healthy data AND window AND visible
prime bound) on ONE explicit object, and proved the one-line bridge from the
orbit-window semi-local gate to `0 <= qw g`.  This module removes the last
quantifier slack of the C3 branch: it composes the pinned detector, the
bridge, and the already-formal contradiction consumer into a single exit
theorem.

* `qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate`: the
  pointwise composition - healthy detector data already carries the
  triple-vanishing field the bridge needs, so the gate alone upgrades any
  healthy detector to a nonnegative same-owner Weil value.
* `sourceRH_of_orbitWindowSemiLocalGate` (HEADLINE): the gate, stated for
  every healthy orbit detector of every hypothetical right-hand off-line
  zero, implies `RHDefinitionBridge.standard.SourceRH`.  All remaining
  C3/P2 content is exactly the single Prop
  `orbitWindowSemiLocalGate`; no detector-design freedom is left open.

This module proves no sign.  The gate itself remains the open P2 obligation
(map `004`); its numerical pricing is a separate record.  RH unclaimed;
GATE 1 mainline untouched.
-/

namespace ConnesWeilRH
namespace Source
namespace C1OrbitWindowExitComposition

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1OrbitWindowSemiLocalGate
open C1SameOwnerWeil
open scoped BigOperators

/-- Pointwise composition: a healthy detector satisfying the orbit-window
semi-local gate has nonnegative same-owner Weil value.  The detector data
already supplies the triple-vanishing premise of the record-1089 bridge. -/
theorem qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (hgate : orbitWindowSemiLocalGate g) :
    0 <= C1SameOwnerWeil.qw g :=
  qw_nonneg_of_orbitWindowSemiLocalGate g hdata.vanishesOnF hgate

/-- HEADLINE exit: if every healthy orbit detector of every hypothetical
right-hand off-line zero satisfies the orbit-window semi-local gate, then
`SourceRH` holds.  Proof: the record-1089 pinned object supplies, for each
such zero, a healthy detector with window and visible-prime bounds; the
pointwise composition turns the gate into `0 <= qw g`; the formal consumer
extracts the contradiction against the strict negativity carried by the
detector data.  This reduces the entire remaining C3/P2 program to the
single Prop `orbitWindowSemiLocalGate`. -/
theorem sourceRH_of_orbitWindowSemiLocalGate
    (hgate : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∀ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g →
          orbitWindowSemiLocalGate g) :
    RHDefinitionBridge.standard.SourceRH := by
  refine healthy_sourceRH_of_right_detector_specific_qw_nonneg ?_
  intro rho hright
  obtain ⟨g, _n, hdata, _hsupport, _hvisible⟩ :=
    exists_pinnedOrbitDetector_with_window_and_visiblePrimes rho
      (fun hcon => by linarith) hright
  exact ⟨g, hdata, qw_nonneg_of_orbitWindowSemiLocalGate g hdata.vanishesOnF
    (hgate rho hright g hdata)⟩

end C1OrbitWindowExitComposition
end Source
end ConnesWeilRH
