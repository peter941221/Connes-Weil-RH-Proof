/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ProlateResponseTraceLegalityUnitScale

/-!
# Audit for trace legality of the finite-S response at unit scale

Focused axiom prints for every declaration in brick #1 (P1) of the Option-C
semi-local bridge: the bounded target prolate factor, the explicit F1'
detector-weighted trace-legality contract, the active-order positive square,
the root-commutator reduction, the source and compression pair owners, and the
response assembly that consumes those contracts.

Record 1063 supplies a numerical guard against raw target-prolate trace
classness, so this module has no raw F1 theorem and no `sorry`.  F1' remains an
explicit analytic input to the consumer; every declaration printed here must use
only the standard axioms.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateResponseTraceLegalityUnitScaleAudit

open ConnesWeilRH.Source.C1ProlateResponseTraceLegalityUnitScale

-- bounded target prolate factor and exact F1' analytic contract
#print axioms targetProlateRemainderFactor
#print axioms targetProlateRemainderFactor_adjoint_comp_self
#print axioms targetProlateRemainderDetectorWeightedTraceLegality
#print axioms targetProlateDetectorRightSmoothingFactor
#print axioms targetProlateDetectorRightSandwich
#print axioms targetProlateDetectorRightSmoothingFactor_adjoint_comp_self
#print axioms targetProlateDetectorRightSmoothingFactorSummable
#print axioms targetProlateDetectorRightSandwichPairData
#print axioms targetProlateDetectorRightSandwichPairData_traceProduct_eq
#print axioms targetProlateDetectorRightSandwich_isTraceClassAlong
#print axioms targetProlateDetectorRootCommutatorRemainder
#print axioms targetProlateDetectorRootCommutatorTraceLegality
#print axioms targetProlateDetectorRootCommutatorTraceLegality_of_pairData
#print axioms rootConvolution_targetProlateRemainder_commutator_eq_neg_threeBranch
#print axioms targetProlateDetectorRootCommutatorTraceLegality_of_threeBranchPairData
#print axioms targetProlateDetectorRootCommutatorRemainder_eq_neg_threeBranch
#print axioms detectorTargetProlate_eq_rightSandwich_add_rootCommutator
#print axioms
  targetProlateRemainderDetectorWeightedTraceLegality_of_rightSmoothing_and_rootCommutator

-- Fourier-compression factors and their pair owners
#print axioms fourierCompressionFactor
#print axioms compressionFactorPairData
#print axioms compressionDifferencePairData
-- single-carrier compression trace product `E Q E` (proven over star projections)
#print axioms fourierCompressionFactor_adjoint_comp_self
#print axioms compressionFactorPairData_traceProduct_eq

-- detector-weighted trace legality of each band piece at unit scale.  The prolate
-- change consumes F1' directly; the compression change is proven from its two
-- explicit HS premises.
#print axioms detectorProlateChange_isTraceClassAlong_at_unit
#print axioms detectorCompressionChange_isTraceClassAlong_at_unit

-- capstone: conditional assembly of selected-detector trace legality at unit scale
#print axioms projectionResponse_isTraceClassAlong_at_unit

end C1ProlateResponseTraceLegalityUnitScaleAudit
end Source
end ConnesWeilRH
