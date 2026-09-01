import ConnesWeilRH.Dev.C1HealthyDetectorEvenOddPair

/-!
# Audit for `C1HealthyDetectorEvenOddPair`

Checks the public surface of the explicit even/odd pair construction and
pins the axiom profile of every headline statement.  The expected axiom base
is exactly `[propext, Classical.choice, Quot.sound]` and `sorryAx` must be
absent.
-/

namespace ConnesWeilRH.Source.C1HealthyDetectorEvenOddPairAudit

open ConnesWeilRH.Source
open ConnesWeilRH.Source.C1HealthyDetectorEvenOddPair

-- public surface
#check @C1HealthyDetectorEvenOddPair.negTest
#check @C1HealthyDetectorEvenOddPair.negTest_apply
#check @C1HealthyDetectorEvenOddPair.laplaceAt_negTest
#check @C1HealthyDetectorEvenOddPair.laplaceAt_reflection
#check @C1HealthyDetectorEvenOddPair.evenPart
#check @C1HealthyDetectorEvenOddPair.oddPart
#check @C1HealthyDetectorEvenOddPair.laplaceAt_evenPart
#check @C1HealthyDetectorEvenOddPair.laplaceAt_oddPart
#check @C1HealthyDetectorEvenOddPair.test_even_evenPart
#check @C1HealthyDetectorEvenOddPair.test_neg_oddPart
#check @C1HealthyDetectorEvenOddPair.support_sumTest_subset
#check @C1HealthyDetectorEvenOddPair.support_negTest
#check @C1HealthyDetectorEvenOddPair.support_evenPart_subset_Icc
#check @C1HealthyDetectorEvenOddPair.support_oddPart_subset_Icc
#check @C1HealthyDetectorEvenOddPair.pairNodeSet
#check @C1HealthyDetectorEvenOddPair.pairNodeTarget
#check @C1HealthyDetectorEvenOddPair.exists_evenOddPair_of_offLineZero

-- axiom pins
#print axioms C1HealthyDetectorEvenOddPair.laplaceAt_reflection
#print axioms C1HealthyDetectorEvenOddPair.laplaceAt_negTest
#print axioms C1HealthyDetectorEvenOddPair.test_even_evenPart
#print axioms C1HealthyDetectorEvenOddPair.test_neg_oddPart
#print axioms C1HealthyDetectorEvenOddPair.support_oddPart_subset_Icc
#print axioms C1HealthyDetectorEvenOddPair.exists_evenOddPair_of_offLineZero

end ConnesWeilRH.Source.C1HealthyDetectorEvenOddPairAudit
