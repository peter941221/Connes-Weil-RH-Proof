/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1LaneRNarrowArch
import ConnesWeilRH.Dev.C1Stage3Characterization
import ConnesWeilRH.Dev.C1SpectralWeil

/-!
# C1 Stage-3 concrete producer (concrete vanishing test first)

The single open bottleneck on the RH mainline is a trace-side
`PositiveTracePairLimitFamily` whose four fields are filled by a genuine analytic
construction rather than left as a conditional contract.  This module closes
Stage 3 for the **first concrete** vanishing test `narrowArchRoot`, per the
"concrete g first" plan, and records exactly why it is non-circular.

Non-circularity (the whole point of this file):

```text
+---------------------------------------------------------------+
| narrowArchRoot_qw_nonneg  (Lane R: prime-free square +        |
| narrow-budget archimedean estimate)                           |
|            |                                                  |
|            v   feeds the sign hypothesis                       |
| positiveTracePairLimitFamily_exists_of_qw_nonnegative         |
|            |                                                  |
|            v                                                   |
| stage3NarrowArchFamily : PositiveTracePairLimitFamily ...     |
|            |                                                  |
|            v   existing order-theoretic consumers              |
| 0 <= qw narrowArchRoot / spectral nonnegativity of its square |
+---------------------------------------------------------------+

The sign is discharged by independent analytic work (Lane R), never by a
trace-family consumer, so constructing the family does not assume its own
conclusion.  This is the concrete stepping stone that de-risks the general
analytic producer; it is NOT yet global spectral nonnegativity over all vanishing
squares (that remains the RH-level obligation).

Firewall note: this active module imports the frozen Lane-R leaf
`C1LaneRNarrowArch` as its first active consumer.  That is a deliberate, recorded
"concrete g validation" touch — the test itself stays frozen-archival; only the
Stage-3 bridge machinery is being exercised on it here.  See docs/1039 and
RH_MAINLINE_FREEZE.md (the change script flags changes under frozen namespaces,
not new importers).
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3ConcreteProducer

open C1LaneRNarrowArch
open C1Stage3Characterization
open C1PositiveTraceLimitBridge

noncomputable section

/-- A genuine Stage-3 positive-trace producer for the concrete vanishing test
`narrowArchRoot`.  The family type is inferred from the rank-one witness; its
sign hypothesis `0 <= qw narrowArchRoot` is filled by the independent Lane-R proof
`narrowArchRoot_qw_nonneg`, so this is a real (non-vacuous) family, not an
assumption smuggled through the trace contract. -/
noncomputable def stage3NarrowArchFamily :=
  positiveTracePairLimitFamily_exists_of_qw_nonnegative
    narrowArchRoot narrowArchRoot_qw_nonneg

/-- The Stage-3 bridge closes on this concrete test: running the genuine family
through the existing order-theoretic consumer yields the same-owner Weil sign.  This
is a re-derivation through the trace contract, confirming the pipeline is
end-to-end and non-circular (the sign entered via Lane R, not via this consumer). -/
theorem stage3NarrowArch_qw_nonneg :
    0 ≤ C1SameOwnerWeil.qw narrowArchRoot :=
  qw_nonnegative_of_positiveTracePairLimitFamily stage3NarrowArchFamily

/-- For the active RH consumer #3 (global spectral nonnegativity), the same family
yields nonnegativity of this concrete vanishing square's exact zero-spectral value. -/
theorem stage3NarrowArch_square_spectral_nonnegative :
    0 ≤ C1SpectralWeil.spectralWeilValue narrowArchRoot.convolutionSquare :=
  spectral_nonnegative_of_positiveTracePairLimitFamily stage3NarrowArchFamily

end
end C1Stage3ConcreteProducer
end Source
end ConnesWeilRH
