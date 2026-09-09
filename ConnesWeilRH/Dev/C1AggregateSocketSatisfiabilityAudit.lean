/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1AggregateSocketSatisfiability

/-!
# C1AggregateSocketSatisfiabilityAudit - axiom prints for record 1226 section 4

Focused `#print axioms` checks for `A1`/`A1b`/`A2`/`A4`.  Every print must
list exactly the three standard axioms; no `sorryAx` may appear in the build
log.
-/

namespace ConnesWeilRH.Source.C1AggregateSocketSatisfiability

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CC20Concrete
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaDetector
open C1BombieriP2Bridge

#print axioms not_bombieriQuadraticAggregateP2BridgeData_of_healthyDetectorData
#print axioms not_nonempty_bombieriQuadraticAggregateP2BridgeData_of_healthyDetectorData
#print axioms no_rightZero_aggregateProducer_witness
#print axioms sourceRH_of_all_vanishing_aggregateSockets

/-- `G3` fidelity example: the `A2` refutation really is about the exact
conjunction shipped in the aggregate consumer premise of
`sourceRH_of_right_bombieriQuadraticAggregateP2BridgeData` (record 1226
section 1, F-D). -/
example (rho : sourceNontrivialZeroSet)
    (hright : (1 / 2 : Real) < rho.1.re)
    (g : CompactLogTest)
    (hdata : HealthyYoshidaDetectorData rho.1 g)
    (hp : Nonempty (BombieriQuadraticAggregateP2BridgeData g)) : False :=
  no_rightZero_aggregateProducer_witness rho hright ⟨g, hdata, hp⟩

end ConnesWeilRH.Source.C1AggregateSocketSatisfiability
