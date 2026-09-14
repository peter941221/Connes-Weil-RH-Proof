/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1MinimalWeilCriterion

/-!
# C1MinimalWeilCriterionAudit - axiom audit for the minimal normal form

Every declaration of `C1MinimalWeilCriterion` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom enters.  The module is pure reassembly - it deletes the
vestigial Mellin vanishing hypothesis from the committed gate and records
that `half` is the only node the certificate chain reads.  It proves no
sign, no positivity, and no inequality about zeta; the wall stays open in
every restated form, and RH is NOT claimed.
-/

open ConnesWeilRH.Source.C1MinimalWeilCriterion

#print axioms vanishesOn_of_subset
#print axioms vanishesOn_empty
#print axioms vanishesOn_singleton_half_iff
#print axioms vanishesOn_half_of_vanishesOn_triple
#print axioms weilGate_of_subset
#print axioms weilGate_triple_iff_sourceRH
#print axioms weilGate_iff_sourceRH_of_subset_triple
#print axioms weilGate_unconditional_iff_sourceRH
#print axioms weilGate_halfOnly_iff_sourceRH
#print axioms poleTerm_convolutionSquare_of_vanishesOn_halfOnly
#print axioms qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_halfOnly
#print axioms qw_eq_neg_archimedeanTerm_of_vanishesOn_halfOnly_of_rootSupport_logTwoHalf
#print axioms qw_nonneg_of_archimedeanTerm_nonpos_of_vanishesOn_halfOnly_of_rootSupport_logTwoHalf
