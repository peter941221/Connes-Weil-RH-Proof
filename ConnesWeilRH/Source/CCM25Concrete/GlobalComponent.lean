/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.Interface

/-!
# CCM25 global QW/Psi formula component

This module packages the global `QW` and `Psi` source rows together with the
global finite-prime evaluator-sum read-off coming from the arithmetic
certificates.  It does not prove the final CCM25-to-CC20 sign bridge.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace GlobalComponent

open FinitePrimeCertificate

structure GlobalFinitePrimeSumReadOff
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  concreteObject :
    FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      W f g lambda
  certificate :
    FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
      W f g lambda
  concreteObject_certificate_eq :
    concreteObject.certificate = certificate
  scopedArithmeticData :
    PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData W f g
  scopedArithmeticData_eq_certificate :
    scopedArithmeticData =
      FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
        certificate
  finitePrimeSumReadOff :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g scopedArithmeticData
  vonMangoldtPairingSumReadOff :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g scopedArithmeticData
  finitePrimeScopedSumReadOff :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g scopedArithmeticData
  vonMangoldtPairingScopedSumReadOff :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g scopedArithmeticData

structure GlobalQWPsiFormulaComponent
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  qwDefinition :
    W.qw f g = W.psi (W.convolutionStar f g)
  psiSign :
    W.psi (W.convolutionStar f g) =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          ∑ n ∈ W.globalPrimeIndexSet,
            W.finitePrimeTerm n (W.convolutionStar f g)
  finitePrimeSumReadOff :
    GlobalFinitePrimeSumReadOff W f g lambda

noncomputable def global_finite_prime_sum_read_off_of_arithmetic_rows
    {W : WeilFormSymbols} (h : Interface.ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    GlobalFinitePrimeSumReadOff W f g lambda :=
  let cert := (h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda
  { concreteObject :=
      FinitePrimeCertificate.concrete_object_of_arithmetic_certificate cert
    certificate := cert
    concreteObject_certificate_eq := rfl
    scopedArithmeticData :=
      FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
        cert
    scopedArithmeticData_eq_certificate := rfl
    finitePrimeSumReadOff :=
      arithmetic_global_mathlib_sum_formula_of_certificate cert
    vonMangoldtPairingSumReadOff :=
      arithmetic_global_mathlib_von_mangoldt_pairing_sum_formula_of_certificate
        cert
    finitePrimeScopedSumReadOff :=
      arithmetic_global_mathlib_sum_formula_of_certificate cert
    vonMangoldtPairingScopedSumReadOff :=
      arithmetic_global_mathlib_von_mangoldt_pairing_sum_formula_of_certificate
        cert }

noncomputable def global_qw_psi_formula_component_of_arithmetic_rows
    {W : WeilFormSymbols} (h : Interface.ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    GlobalQWPsiFormulaComponent W f g lambda where
  oneLtLambda := hlambda
  qwDefinition :=
    Interface.qw_definition_of_arithmetic_rows h f g
  psiSign :=
    Interface.psi_sign_of_arithmetic_rows h (W.convolutionStar f g)
  finitePrimeSumReadOff :=
    global_finite_prime_sum_read_off_of_arithmetic_rows
      h f g lambda hlambda

theorem qw_definition_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.qw f g = W.psi (W.convolutionStar f g) :=
  h.qwDefinition

theorem psi_sign_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.psi (W.convolutionStar f g) =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          ∑ n ∈ W.globalPrimeIndexSet,
            W.finitePrimeTerm n (W.convolutionStar f g) :=
  h.psiSign

def global_concrete_object_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      W f g lambda :=
  h.finitePrimeSumReadOff.concreteObject

noncomputable def GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
    (W : WeilFormSymbols) (f g : TestFunction)
    (data : PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
      W f g) : ℝ :=
  ∑ n ∈ W.globalPrimeIndexSet,
    if hn : n ∈ W.globalPrimeIndexSet then
      let atom := data.atIndex n hn
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue))
    else 0

theorem global_concrete_object_certificate_eq
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (global_concrete_object_of_component h).certificate =
      h.finitePrimeSumReadOff.certificate :=
  h.finitePrimeSumReadOff.concreteObject_certificate_eq

theorem global_finite_prime_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.finitePrimeSumReadOff

theorem global_finite_prime_scoped_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.finitePrimeScopedSumReadOff

theorem global_finite_prime_sum_from_concrete_object
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.finitePrimeSumReadOff

theorem global_von_mangoldt_pairing_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.vonMangoldtPairingSumReadOff

theorem global_von_mangoldt_pairing_scoped_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.vonMangoldtPairingScopedSumReadOff

theorem global_von_mangoldt_pairing_sum_from_concrete_object
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.vonMangoldtPairingSumReadOff

theorem global_index_prime_power_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  PrimePowerArithmetic.source_on_index_set_prime_power_index
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem global_index_source_atom_visible_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) :=
  (h.finitePrimeSumReadOff.scopedArithmeticData.atIndex n hn).sourceAtomVisible

theorem global_index_weight_read_off_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  PrimePowerArithmetic.source_on_index_set_weight_read_off
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem global_index_pairing_formula_source_evaluations_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom := h.finitePrimeSumReadOff.scopedArithmeticData.atIndex n hn
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.forwardValue +
          atom.sourcePairing.model.sourceEvaluation.inverseValue) :=
  PrimePowerArithmetic.source_on_index_set_pairing_formula_source_evaluations
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem global_index_finite_prime_term_formula_source_evaluations_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom := h.finitePrimeSumReadOff.scopedArithmeticData.atIndex n hn
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_mathlib_source_evaluations
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem global_index_von_mangoldt_pairing_formula_source_evaluations_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom := h.finitePrimeSumReadOff.scopedArithmeticData.atIndex n hn
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_on_index_set_von_mangoldt_pairing_product_formula_source_evaluations
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem global_finite_prime_source_evaluations_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
        W f g h.finitePrimeSumReadOff.scopedArithmeticData := by
  dsimp [GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simpa [hn] using
    global_index_finite_prime_term_formula_source_evaluations_of_component h hn

theorem global_von_mangoldt_pairing_source_evaluations_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
        W f g h.finitePrimeSumReadOff.scopedArithmeticData := by
  dsimp [GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simpa [hn] using
    global_index_von_mangoldt_pairing_formula_source_evaluations_of_component
      h hn

theorem global_finite_prime_mathlib_pairing_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      ∑ n ∈ W.globalPrimeIndexSet,
        ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f g := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact
    PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_mathlib_pairing
      h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem global_von_mangoldt_mathlib_pairing_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      ∑ n ∈ W.globalPrimeIndexSet,
        ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f g := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [global_index_weight_read_off_of_component h hn]

theorem psi_source_evaluator_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.psi (W.convolutionStar f g) =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            W f g h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.psiSign, global_finite_prime_sum_of_component h]

theorem psi_scoped_source_evaluator_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.psi (W.convolutionStar f g) =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            W f g h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.psiSign, global_finite_prime_scoped_sum_of_component h]

theorem psi_source_evaluations_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.psi (W.convolutionStar f g) =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
            W f g h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.psiSign, global_finite_prime_source_evaluations_sum_of_component h]

theorem psi_mathlib_pairing_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.psi (W.convolutionStar f g) =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          ∑ n ∈ W.globalPrimeIndexSet,
            ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f g := by
  rw [h.psiSign, global_finite_prime_mathlib_pairing_sum_of_component h]

theorem qw_source_evaluator_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.qw f g =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            W f g h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.qwDefinition, psi_source_evaluator_of_component h]

theorem qw_scoped_source_evaluator_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.qw f g =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            W f g h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.qwDefinition, psi_scoped_source_evaluator_of_component h]

theorem qw_source_evaluations_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.qw f g =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
            W f g h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.qwDefinition, psi_source_evaluations_of_component h]

theorem qw_mathlib_pairing_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.qw f g =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          ∑ n ∈ W.globalPrimeIndexSet,
            ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f g := by
  rw [h.qwDefinition, psi_mathlib_pairing_sum_of_component h]

end GlobalComponent
end CCM25Concrete
end Source
end ConnesWeilRH
