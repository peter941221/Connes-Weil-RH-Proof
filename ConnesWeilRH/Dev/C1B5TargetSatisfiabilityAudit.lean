/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1B5TargetSatisfiability

/-!
# C1B5TargetSatisfiabilityAudit - axiom prints for record 1225 section 3

Four focused `#print axioms` checks for `L1`-`L4`.  Every print must list
exactly the three standard axioms; no `sorryAx` may appear in the build log.
-/

namespace ConnesWeilRH.Source.C1B5TargetSatisfiability

open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CC20Concrete
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaDetector
open Dev.C1Stage3ProjectionOperatorFamily

#print axioms qw_neg_of_healthyDetectorData
#print axioms not_healthy_of_projectionCutoffContracts
#print axioms no_rightZero_b5Producer_witness
#print axioms sourceRH_of_all_vanishing_projectionContracts

/-- `G3` fidelity example: the `L3` refutation really is about the exact
conjunction shipped in the B5 consumer premise (record 1225 section 1, F3). -/
example {ν : Type*} (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (rho : sourceNontrivialZeroSet)
    (hright : (1 / 2 : Real) < rho.1.re)
    (g : CompactLogTest)
    (hg : HealthyYoshidaDetectorData rho.1 g)
    (hcontracts :
      Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis)) : False :=
  not_healthy_of_projectionCutoffContracts lambda S globalBasis hcontracts hg

end ConnesWeilRH.Source.C1B5TargetSatisfiability
