import ConnesWeilRH.Dev.M2WidthPlateau

/-!
# C1RouteRepairAudit - focused trust audit for the repaired C1 route

This import-facing module checks the coordinate bridge, same-owner Weil
readbacks, sign convention, and M2 compatibility theorem. It adds no
mathematical assumptions or route producer.
-/

#print axioms ConnesWeilRH.Source.C1LogPositiveBridge.positiveRouteRaw_contDiff
#print axioms ConnesWeilRH.Source.C1LogPositiveBridge.mellin_toPositiveRouteTest_eq_laplaceAt
#print axioms ConnesWeilRH.Source.C1SameOwnerWeil.poleTerm_square_eq_selected
#print axioms ConnesWeilRH.Source.C1SameOwnerWeil.finitePrimeSum_square_eq_selected
#print axioms ConnesWeilRH.Source.C1SameOwnerWeil.archimedeanTerm_square_eq_selected
#print axioms ConnesWeilRH.Source.C1.healthyRouteMellinReadoff
#print axioms ConnesWeilRH.Source.C1.healthyWeilSquareReadoff
#print axioms ConnesWeilRH.Source.C1.healthyCC20WeilNonpositive_iff_qw_nonnegative
#print axioms ConnesWeilRH.Source.C1.healthyCriterionState_iff_all_vanishing_qw_nonnegative
#print axioms ConnesWeilRH.Source.Dev.M2Width.healthyQw_eq_neg_weilLocalSum
