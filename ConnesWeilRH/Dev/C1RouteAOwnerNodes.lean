/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1RouteAOwnerTest
import ConnesWeilRH.Dev.C1RouteAGridSampling

/-!
# The owner strip residual is the 101 node values (record 2317)

Record 2313's consumer `frozenStripHypothesis_of_certified_nodes` takes two
`CompactLogTest`s, their support bounds, and node min-product bounds at the
101 grid nodes `j / 100`, `-50 <= j <= 50`; record 2315 packaged the
corrected width-a^2 owner as a `CompactLogTest` for arbitrary coefficient
and modulation vectors and proved its support bound.  This module closes the
loop: for the owner pair

    b = correctedPhysical baseCoefficients modulations
    c = correctedPhysical corrCoefficients modulations

(the shape of the record 2275 capture: one shared modulation vector, two
coefficient vectors), the strip hypothesis `FrozenStripHypothesis b c`
follows from the node bounds ALONE — the support bounds are discharged by
record 2315, and the node hypothesis is stated over the raw owner functions
`correctedPhysical`, exactly the quantity the record 2316 node table
certifies:

    stripSecondNorm (j/100) b * stripNorm (j/100) c   and the mirror term
    min(...) <= stripGridMax2303     at the 101 nodes j/100.

Main declaration:

* `frozenStripHypothesis_of_owner_nodes` — the instantiation, whose only
  remaining hypothesis is the 101-node bound of the record 2316 table.

The coefficient and modulation vectors stay free: the numeric instantiation
to the captured vectors is artifact-grade (records 2275/2303/2316).  No
producer GO, no gate sign change, no RH claim.
-/

namespace ConnesWeilRH
namespace Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-- **Owner strip hypothesis from the 101 node values (record 2317).**  The
record 2313 certified-node consumer instantiated with the record 2315
packaged owner pair: support bounds are supplied by
`correctedPhysicalCompactLogTest_tsupport_subset`, and the only residual
hypothesis is the node min-product bound at the 101 grid nodes `j / 100`,
`-50 <= j <= 50` — the raw-owner shape certified by the record 2316 node
table.  The vectors stay free. -/
theorem frozenStripHypothesis_of_owner_nodes
    (baseCoefficients corrCoefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ)
    (hnode : ∀ j : ℤ, -(50 : ℤ) ≤ j → j ≤ 50 →
      min (stripSecondNorm ((j : ℝ) / 100)
            (correctedPhysical baseCoefficients modulations) *
           stripNorm ((j : ℝ) / 100)
            (correctedPhysical corrCoefficients modulations))
          (stripSecondNorm ((j : ℝ) / 100)
            (correctedPhysical corrCoefficients modulations) *
           stripNorm ((j : ℝ) / 100)
            (correctedPhysical baseCoefficients modulations))
        ≤ stripGridMax2303) :
    FrozenStripHypothesis
      (correctedPhysicalCompactLogTest baseCoefficients modulations)
      (correctedPhysicalCompactLogTest corrCoefficients modulations) := by
  refine frozenStripHypothesis_of_certified_nodes _ _ ?_ ?_ ?_
  · exact correctedPhysicalCompactLogTest_tsupport_subset baseCoefficients modulations
  · exact correctedPhysicalCompactLogTest_tsupport_subset corrCoefficients modulations
  · intro j hjlo hjhi
    rw [correctedPhysicalCompactLogTest_toFun baseCoefficients modulations,
      correctedPhysicalCompactLogTest_toFun corrCoefficients modulations]
    exact hnode j hjlo hjhi

end Dev
end ConnesWeilRH
