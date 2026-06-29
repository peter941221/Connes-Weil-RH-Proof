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
  finitePrimeSumReadOff :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda certificate.atoms
  vonMangoldtPairingSumReadOff :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda certificate.atoms

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
    RestrictedFinitePrimeSumReadOff W f g lambda where
  concreteObject :=
    Interface.fixed_lambda_concrete_object_of_arithmetic_rows
      h f g lambda hlambda
  certificate :=
    (h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda
  concreteObject_certificate_eq :=
    Interface.fixed_lambda_concrete_object_certificate_eq h f g lambda hlambda
  finitePrimeSumReadOff :=
    Interface.arithmetic_restricted_sum_formula_of_arithmetic_rows
      h f g lambda hlambda
  vonMangoldtPairingSumReadOff :=
    Interface.arithmetic_restricted_von_mangoldt_pairing_sum_formula_of_arithmetic_rows
      h f g lambda hlambda

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
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f f lambda h.finitePrimeSumReadOff.certificate.atoms :=
  h.finitePrimeSumReadOff.finitePrimeSumReadOff

theorem restricted_finite_prime_sum_from_concrete_object
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f f lambda
          (restricted_concrete_object_of_component h).certificate.atoms := by
  exact
    (restricted_concrete_object_of_component h).restrictedFinitePrimeTermSumReadOff

theorem restricted_von_mangoldt_pairing_sum_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f f lambda h.finitePrimeSumReadOff.certificate.atoms :=
  h.finitePrimeSumReadOff.vonMangoldtPairingSumReadOff

theorem restricted_von_mangoldt_pairing_sum_from_concrete_object
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f f lambda
          (restricted_concrete_object_of_component h).certificate.atoms := by
  exact
    (restricted_concrete_object_of_component h).restrictedVonMangoldtPairingSumReadOff

theorem qw_lambda_formula_source_evaluator_of_component
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : RestrictedQWLambdaFormulaComponent W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
            W f f lambda h.finitePrimeSumReadOff.certificate.atoms := by
  rw [h.qwLambdaFormula,
    restricted_von_mangoldt_pairing_sum_of_component h]

end RestrictedComponent
end CCM25Concrete
end Source
end ConnesWeilRH
