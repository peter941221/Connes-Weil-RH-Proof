/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1GateMatrixRepresentation

/-!
# Record 1121 audit: T2-rep gate-matrix representation

Focused axiom audit for every public declaration introduced by
`C1GateMatrixRepresentation`.  The representation is consumed only by the
healthy-`CompactLog`, detector-specific Stage-B route; it asserts no sign and
does not claim RH.
-/

open ConnesWeilRH Source C1GateMatrixRepresentation

#print axioms spanObj
#print axioms spanObj_apply
#print axioms pairTest
#print axioms pairTest_self
#print axioms gateMatrix
#print axioms pairIntegrand_integrable
#print axioms pairTest_apply_of_abs_ge
#print axioms pairTest_support
#print axioms packedSum
#print axioms packedSum_apply
#print axioms packedSum_support
#print axioms archimedeanIntegrand_packedSum
#print axioms integrableOn_archimedeanIntegrand_packedSum
#print axioms ICgate_zero_of_test_zero
#print axioms ICgate_packedSum
#print axioms convolutionSquare_spanObj_apply
#print axioms pairPiece
#print axioms gate_sum_span
#print axioms pair_gate_sum_eq_qform
#print axioms gate_qform_span
#print axioms hrep_of_gateMatrix_eq

namespace ConnesWeilRH.Source.C1GateMatrixRepresentation

open CCM25Concrete.CompactLogConvolution
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open Matrix
open scoped BigOperators

/-- Fidelity: `hrep_of_gateMatrix_eq` returns the literal representation slot
consumed by the T2 absolute headlines. -/
example {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    (M_true : Matrix (Fin k) (Fin k) ℝ) (hM : gateMatrix w = M_true)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B)
    (hI : ∀ i j, MeasureTheory.IntegrableOn
      (archimedeanIntegrand (pairTest w i j)) (Set.Ioi (0 : ℝ))) :
    ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (M_true *ᵥ y) :=
  hrep_of_gateMatrix_eq w y M_true hM hw hI

end ConnesWeilRH.Source.C1GateMatrixRepresentation
