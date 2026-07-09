/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.Interface

/-!
# CCM25 restricted QW_lambda formula component

This module packages the restricted `QW_lambda` formula together with the
finite-prime evaluator-sum read-off coming from the arithmetic certificates.
It does not prove restricted-to-full equality.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace RestrictedComponent

open FinitePrimeCertificate
open PrimePowerArithmetic

structure RestrictedFinitePrimeSumReadOff
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
    PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
      W f g lambda
  scopedArithmeticData_eq_certificate :
    scopedArithmeticData =
      FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
        certificate
  finitePrimeSumReadOff :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda scopedArithmeticData
  vonMangoldtPairingSumReadOff :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda scopedArithmeticData
  finitePrimeScopedSumReadOff :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda scopedArithmeticData
  vonMangoldtPairingScopedSumReadOff :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda scopedArithmeticData

structure RestrictedQWLambdaFormulaComponent
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  qwLambdaFormula :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          ∑ n ∈ W.restrictedPrimeIndexSet lambda,
            W.vonMangoldtWeight n * W.primePowerPairing n f f
  finitePrimeSumReadOff :
    RestrictedFinitePrimeSumReadOff W f f lambda

noncomputable def restricted_finite_prime_sum_read_off_of_arithmetic_rows
    {W : WeilFormSymbols} (h : Interface.ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    RestrictedFinitePrimeSumReadOff W f g lambda :=
  let cert := (h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda
  { concreteObject :=
      FinitePrimeCertificate.concrete_object_of_arithmetic_certificate cert
    certificate := cert
    concreteObject_certificate_eq := rfl
    scopedArithmeticData :=
      FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
        cert
    scopedArithmeticData_eq_certificate := rfl
    finitePrimeSumReadOff :=
      arithmetic_restricted_mathlib_sum_formula_of_certificate
        cert
    vonMangoldtPairingSumReadOff :=
      arithmetic_restricted_mathlib_von_mangoldt_pairing_sum_formula_of_certificate
        cert
    finitePrimeScopedSumReadOff :=
      arithmetic_restricted_mathlib_sum_formula_of_certificate
        cert
    vonMangoldtPairingScopedSumReadOff :=
      arithmetic_restricted_mathlib_von_mangoldt_pairing_sum_formula_of_certificate
        cert }

noncomputable def restricted_qw_lambda_formula_component_of_arithmetic_rows
    {W : WeilFormSymbols} (h : Interface.ConcreteCCM25ArithmeticRows W)
    (f : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    RestrictedQWLambdaFormulaComponent W f lambda where
  oneLtLambda := hlambda
  qwLambdaFormula :=
    Interface.qw_lambda_formula_of_arithmetic_rows h lambda hlambda f
  finitePrimeSumReadOff :=
    restricted_finite_prime_sum_read_off_of_arithmetic_rows
      h f f lambda hlambda

theorem qw_lambda_formula_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          ∑ n ∈ W.restrictedPrimeIndexSet lambda,
            W.vonMangoldtWeight n * W.primePowerPairing n f f :=
  h.qwLambdaFormula

def restricted_concrete_object_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      W f f lambda :=
  h.finitePrimeSumReadOff.concreteObject

noncomputable def RestrictedSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ)
    (data : PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
      W f f lambda) : ℝ :=
  ∑ n ∈ W.restrictedPrimeIndexSet lambda,
    if hn : n ∈ W.restrictedPrimeIndexSet lambda then
      let atom := data.atIndex n hn
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue))
    else 0

theorem restricted_concrete_object_certificate_eq
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (restricted_concrete_object_of_component h).certificate =
      h.finitePrimeSumReadOff.certificate :=
  h.finitePrimeSumReadOff.concreteObject_certificate_eq

theorem restricted_finite_prime_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f f lambda h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.finitePrimeSumReadOff

theorem restricted_finite_prime_scoped_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f f lambda h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.finitePrimeScopedSumReadOff

theorem restricted_finite_prime_sum_from_concrete_object
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f f lambda h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.finitePrimeSumReadOff

theorem restricted_von_mangoldt_pairing_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f f lambda h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.vonMangoldtPairingSumReadOff

theorem restricted_von_mangoldt_pairing_scoped_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f f lambda h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.vonMangoldtPairingScopedSumReadOff

theorem restricted_von_mangoldt_pairing_sum_from_concrete_object
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f f lambda h.finitePrimeSumReadOff.scopedArithmeticData :=
  h.finitePrimeSumReadOff.vonMangoldtPairingSumReadOff

theorem restricted_index_prime_power_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  PrimePowerArithmetic.source_on_index_set_prime_power_index
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem restricted_index_source_atom_visible_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeAtomVisible n (W.convolutionStar f f) :=
  (h.finitePrimeSumReadOff.scopedArithmeticData.atIndex n hn).sourceAtomVisible

theorem restricted_index_weight_read_off_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  PrimePowerArithmetic.source_on_index_set_weight_read_off
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem restricted_index_pairing_formula_source_evaluations_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom := h.finitePrimeSumReadOff.scopedArithmeticData.atIndex n hn
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.forwardValue +
          atom.sourcePairing.model.sourceEvaluation.inverseValue) :=
  PrimePowerArithmetic.source_on_index_set_pairing_formula_source_evaluations
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem restricted_index_finite_prime_term_formula_source_evaluations_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom := h.finitePrimeSumReadOff.scopedArithmeticData.atIndex n hn
    W.finitePrimeTerm n (W.convolutionStar f f) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_mathlib_source_evaluations
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem restricted_index_von_mangoldt_pairing_formula_source_evaluations_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom := h.finitePrimeSumReadOff.scopedArithmeticData.atIndex n hn
    W.vonMangoldtWeight n * W.primePowerPairing n f f =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_on_index_set_von_mangoldt_pairing_product_formula_source_evaluations
    h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem restricted_finite_prime_source_evaluations_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      RestrictedSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
        W f lambda h.finitePrimeSumReadOff.scopedArithmeticData := by
  dsimp [RestrictedSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simpa [hn] using
    restricted_index_finite_prime_term_formula_source_evaluations_of_component
      h hn

theorem restricted_von_mangoldt_pairing_source_evaluations_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      RestrictedSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
        W f lambda h.finitePrimeSumReadOff.scopedArithmeticData := by
  dsimp [RestrictedSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simpa [hn] using
    restricted_index_von_mangoldt_pairing_formula_source_evaluations_of_component
      h hn

theorem restricted_finite_prime_mathlib_pairing_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      ∑ n ∈ W.restrictedPrimeIndexSet lambda,
        ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f f := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact
    PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_mathlib_pairing
      h.finitePrimeSumReadOff.scopedArithmeticData hn

theorem restricted_von_mangoldt_mathlib_pairing_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      ∑ n ∈ W.restrictedPrimeIndexSet lambda,
        ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f f := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [restricted_index_weight_read_off_of_component h hn]

theorem qw_lambda_formula_source_evaluator_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
            W f f lambda h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.qwLambdaFormula,
    restricted_von_mangoldt_pairing_sum_of_component h]

theorem qw_lambda_formula_scoped_source_evaluator_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
            W f f lambda h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.qwLambdaFormula,
    restricted_von_mangoldt_pairing_scoped_sum_of_component h]

theorem qw_lambda_formula_source_evaluations_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          RestrictedSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
            W f lambda h.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [h.qwLambdaFormula,
    restricted_von_mangoldt_pairing_source_evaluations_sum_of_component h]

theorem qw_lambda_formula_mathlib_pairing_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          ∑ n ∈ W.restrictedPrimeIndexSet lambda,
            ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f f := by
  rw [h.qwLambdaFormula,
    restricted_von_mangoldt_mathlib_pairing_sum_of_component h]

end RestrictedComponent
end CCM25Concrete
end Source
end ConnesWeilRH
