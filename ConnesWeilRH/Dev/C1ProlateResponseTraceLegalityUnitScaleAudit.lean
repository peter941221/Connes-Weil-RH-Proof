/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ProlateResponseTraceLegalityUnitScale

/-!
# Audit for trace legality of the finite-S response at unit scale

Focused axiom prints for every declaration in brick #1 (P1) of the Option-C
semi-local bridge: the target prolate factor and its `A^dagger A` owner, the
prolate / compression pair owners, and the detector-weighted decomposition that
discharges the Gate-2 readback premise at the canonical unit scale.

The two load-bearing cruxes — F1 (target prolate factor Hilbert--Schmidt) and
F2 (Fourier-compression factors Hilbert--Schmidt) — still carry `sorry` while
their analytic content is being written; their prints show `sorryAx`.  Every
plumbing declaration must print only the three standard axioms.  The capstone
and the prolate-path theorem inherit `sorryAx` transitively from F1/F2 until
those land.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateResponseTraceLegalityUnitScaleAudit

open ConnesWeilRH.Source.C1ProlateResponseTraceLegalityUnitScale

-- target prolate factor and its positive-square identification
#print axioms targetProlateHilbertSchmidtFactor
#print axioms targetProlateHilbertSchmidtFactor_adjoint_comp_self

-- F1 reduction plumbing + the isolated semilocal prolate-remainder crux it reduces to
-- (the diagonal identity is proved; the trace-class crux still carries sorryAx until round 2)
#print axioms targetProlateHilbertSchmidtFactor_unit_diagonal_eq_targetRemainder
#print axioms targetProlateRemainder_unit_isTraceClassAlong

-- F1 crux (now proven plumbing over the semilocal trace-class crux above)
#print axioms targetProlateHilbertSchmidtFactor_unit_summable

-- target prolate pair owner and its trace product
#print axioms targetProlatePairData
#print axioms targetProlatePairData_traceProduct_eq

-- the signed prolate band difference as an l2Sum pair owner
#print axioms prolateDifferencePairData
#print axioms prolateDifferencePairData_traceProduct_eq

-- Fourier-compression factors and their pair owners
#print axioms fourierCompressionFactor
#print axioms compressionFactorPairData
#print axioms compressionDifferencePairData
-- single-carrier compression trace product `E Q E` (proven over star projections)
#print axioms fourierCompressionFactor_adjoint_comp_self
#print axioms compressionFactorPairData_traceProduct_eq

-- detector-weighted trace legality of each band piece at unit scale.  The prolate
-- change inherits the F1 semilocal crux transitively; the compression change is
-- proven from its two HS premises and carries no sorryAx of its own.
#print axioms detectorProlateChange_isTraceClassAlong_at_unit
#print axioms detectorCompressionChange_isTraceClassAlong_at_unit

-- capstone: the selected-detector response is trace-class at unit scale
#print axioms projectionResponse_isTraceClassAlong_at_unit

end C1ProlateResponseTraceLegalityUnitScaleAudit
end Source
end ConnesWeilRH
