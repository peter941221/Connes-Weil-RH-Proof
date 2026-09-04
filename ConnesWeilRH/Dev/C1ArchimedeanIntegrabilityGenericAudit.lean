/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ArchimedeanIntegrabilityGeneric

/-!
# Record 1122 audit: generic archimedean integrability

Focused axiom audit for every public declaration introduced by
`C1ArchimedeanIntegrabilityGeneric`.  The record discharges the 1121
per-pair legality hypothesis; it asserts no sign and does not claim RH.
-/

open ConnesWeilRH Source C1ArchimedeanIntegrabilityGeneric

#print axioms archimedeanNumerator_contDiff
#print axioms archimedeanNumeratorRe
#print axioms archimedeanNumeratorIm
#print axioms archimedeanNumeratorRe_contDiff
#print axioms archimedeanNumeratorIm_contDiff
#print axioms archimedeanNumeratorRe_zero
#print axioms archimedeanNumeratorIm_zero
#print axioms archimedeanIntegrand_continuousOn_Ioi
#print axioms tendsto_archimedeanNumeratorRe_div_denominator_nhdsGT
#print axioms tendsto_archimedeanNumeratorIm_div_denominator_nhdsGT
#print axioms archimedeanIntegrandLimit
#print axioms tendsto_archimedeanIntegrand_nhdsGT
#print axioms eventually_archimedeanIntegrand_eq_tail
#print axioms archimedeanIntegrand_isBigO_exp_neg
#print axioms integrableOn_archimedeanIntegrand
#print axioms pairTest_legality
#print axioms gate_sum_span_free
#print axioms gate_qform_span_free
#print axioms hrep_of_gateMatrix_eq_free

namespace ConnesWeilRH.Source.C1ArchimedeanIntegrabilityGeneric

open CCM25Concrete.CompactLogConvolution
open C1GateMatrixRepresentation
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open Matrix
open scoped BigOperators

/-- Fidelity: the 1121 named legality hypothesis holds for an abstract pair
of window tests, with no data input. -/
example {k : ℕ} (w : Fin k → CompactLogTest) (i j : Fin k) :
    MeasureTheory.IntegrableOn
      (archimedeanIntegrand (pairTest w i j)) (Set.Ioi (0 : ℝ)) :=
  pairTest_legality w i j

/-- Fidelity: `hrep_of_gateMatrix_eq_free` returns the literal representation
slot consumed by the T2 absolute headlines, with NO legality hypothesis. -/
example {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    (M_true : Matrix (Fin k) (Fin k) ℝ) (hM : gateMatrix w = M_true)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B) :
    ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (M_true *ᵥ y) :=
  hrep_of_gateMatrix_eq_free w y M_true hM hw

end ConnesWeilRH.Source.C1ArchimedeanIntegrabilityGeneric
