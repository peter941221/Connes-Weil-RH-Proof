import ConnesWeilRH.Dev.C1Stage3ProjectionKernel

open ConnesWeilRH.Source.C1Stage3ProjectionKernel

-- Gate 0: the positive core lives in the active namespace and is non-circular.
#print axioms stage3ProjectionKernel_isPositive

-- Gate 1 (operator identity / algebraic backbone): conjugating the kernel by any
-- bounded factor keeps it positive on the source space.
#print axioms stage3ProjectionKernel_adjointConj_isPositive
