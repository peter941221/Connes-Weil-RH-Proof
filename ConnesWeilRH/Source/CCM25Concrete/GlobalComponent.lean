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
  finitePrimeSumReadOff :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g certificate.atoms
  vonMangoldtPairingSumReadOff :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g certificate.atoms

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
    GlobalFinitePrimeSumReadOff W f g lambda where
  concreteObject :=
    Interface.fixed_lambda_concrete_object_of_arithmetic_rows
      h f g lambda hlambda
  certificate :=
    (h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda
  concreteObject_certificate_eq :=
    Interface.fixed_lambda_concrete_object_certificate_eq h f g lambda hlambda
  finitePrimeSumReadOff :=
    Interface.arithmetic_global_sum_formula_of_arithmetic_rows
      h f g lambda hlambda
  vonMangoldtPairingSumReadOff :=
    Interface.arithmetic_global_von_mangoldt_pairing_sum_formula_of_arithmetic_rows
      h f g lambda hlambda

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
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g h.finitePrimeSumReadOff.certificate.atoms :=
  h.finitePrimeSumReadOff.finitePrimeSumReadOff

theorem global_finite_prime_sum_from_concrete_object
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g (global_concrete_object_of_component h).certificate.atoms := by
  exact (global_concrete_object_of_component h).globalFinitePrimeTermSumReadOff

theorem global_von_mangoldt_pairing_sum_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g h.finitePrimeSumReadOff.certificate.atoms :=
  h.finitePrimeSumReadOff.vonMangoldtPairingSumReadOff

theorem global_von_mangoldt_pairing_sum_from_concrete_object
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g (global_concrete_object_of_component h).certificate.atoms := by
  exact (global_concrete_object_of_component h).globalVonMangoldtPairingSumReadOff

theorem psi_source_evaluator_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.psi (W.convolutionStar f g) =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
            W f g h.finitePrimeSumReadOff.certificate.atoms := by
  rw [h.psiSign, global_finite_prime_sum_of_component h]

theorem qw_source_evaluator_of_component
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : GlobalQWPsiFormulaComponent W f g lambda) :
    W.qw f g =
      W.poleFunctional (W.convolutionStar f g) -
        W.archimedeanTerm (W.convolutionStar f g) -
          PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
            W f g h.finitePrimeSumReadOff.certificate.atoms := by
  rw [h.qwDefinition, psi_source_evaluator_of_component h]

end GlobalComponent
end CCM25Concrete
end Source
end ConnesWeilRH
