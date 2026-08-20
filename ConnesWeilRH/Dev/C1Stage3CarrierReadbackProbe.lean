import ConnesWeilRH.Dev.C1Stage3CarrierReadback

open ConnesWeilRH.Source.C1Stage3CarrierReadback

-- Gate 2 arithmetic readback: Re Tr(projectionResponse) = selectedArithmeticCarrierSum + Re residual.
-- Axiom audit must stay clean (no sorryAx): expected [propext, Classical.choice, Quot.sound].
#print axioms selectedArithmeticCarrierSum
#print axioms stage3CarrierReadback_arithmetic_eq_selectedRealSum_residual
