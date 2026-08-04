/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Basic

/-!
# A0 window-gate rejection guards

The running skeleton's `hilbertSchmidtGate g = traceClass g ∧ cyclicLegal g`
(Basic.lean:129 + `LegalSquareTraceScaleSymbols.hilbertSchmidtGate`
TraceScale.lean:288) is concretely realized over the single-point window
`defaultWindow = (0, 0)` (AnalyticCoreBase.lean:3102).  Both the physical
support (`traceClass g = supportCarrier g ⊆ windowCarrier (0,0)`) and the
Fourier support (`cyclicLegal g = fourierSupportCarrier (𝓕 g) ⊆ windowCarrier
(0,0)`) must sit inside the same single-point carrier `{(0,0)}`.

These guards record the concrete carrier facts that make the gate an EMPTY
producer on this window: the window carrier is the singleton `{((0,0))}`, so a
compact test nonzero away from 0 has windowed support empty (its `traceClass`
is vacuous-true), while its Fourier image cannot be forced into that single
point.  Consequently the single-point-window model cannot supply a nonzero
gate test (AGENTS §6 empty producer).
-/

namespace ConnesWeilRH
namespace Dev
namespace A0WindowGateGuard

open Source
open Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
open Source.AnalyticCore.SourceConcreteBaseLayer

/--
The concrete single-point window carrier is the singleton `{(0,0)}` with
log-scale coordinate `0` and base-window coordinate `0`.
-/
theorem pointInConcreteWindow_defaultWindow_iff
    (x : ConcreteSupportPoint) :
    pointInConcreteWindow defaultWindow x ↔ x.1 = 0 ∧ x.2 = 0 := by
  unfold pointInConcreteWindow defaultWindow
  constructor
  · rintro ⟨h0le, hle0, hz⟩
    exact ⟨le_antisymm hle0 h0le, hz⟩
  · rintro ⟨hx1, hx2⟩
    rw [hx1]
    exact ⟨le_rfl, le_rfl, hx2⟩

end A0WindowGateGuard
end Dev
end ConnesWeilRH