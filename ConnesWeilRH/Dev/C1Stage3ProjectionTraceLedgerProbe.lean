import ConnesWeilRH.Dev.C1Stage3ProjectionTraceLedger

open ConnesWeilRH.Source.C1Stage3ProjectionTraceLedger

-- Gate 2 carrier-side ledger: the projection response trace splits into the finite
-- prime-term sum plus the residual.  Axiom audit must stay clean (no sorryAx).
#print axioms stage3ProjectionResponse_eq_arithmetic_add_residual
#print axioms stage3TraceLedger_projectionResponse_eq_finitePrimeSum_add_residual
