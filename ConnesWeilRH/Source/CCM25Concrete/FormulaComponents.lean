/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.GlobalComponent
import ConnesWeilRH.Source.CCM25Concrete.RestrictedComponent

/-!
# Combined CCM25 formula components

This module bundles the global `QW/Psi` component and the restricted
`QW_lambda` component for one fixed test and cutoff.  It is a source-object
boundary for later sign and restricted-to-full bridges; it does not prove those
bridges.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FormulaComponents

structure ConcreteCCM25FormulaComponents
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ) where
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f f
  commonCertificate :
    FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
      W f f lambda
  commonCertificateSourceTest :
    commonCertificate.support.sourceTest = sourceTest
  global :
    GlobalComponent.GlobalQWPsiFormulaComponent W f f lambda
  restricted :
    RestrictedComponent.RestrictedQWLambdaFormulaComponent W f lambda
  globalCertificate_eq_common :
    global.finitePrimeSumReadOff.certificate = commonCertificate
  restrictedCertificate_eq_common :
    restricted.finitePrimeSumReadOff.certificate = commonCertificate

def formula_components_of_arithmetic_rows
    {W : WeilFormSymbols} (h : Interface.ConcreteCCM25ArithmeticRows W)
    (f : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ConcreteCCM25FormulaComponents W f lambda where
  sourceTest :=
    Interface.source_test_of_arithmetic_rows h f f
  commonCertificate :=
    (h.finitePrimeArithmeticCertificates f f).certificate lambda hlambda
  commonCertificateSourceTest :=
    Interface.arithmetic_certificate_source_test_of_arithmetic_rows
      h f f lambda hlambda
  global :=
    GlobalComponent.global_qw_psi_formula_component_of_arithmetic_rows
      h f f lambda hlambda
  restricted :=
    RestrictedComponent.restricted_qw_lambda_formula_component_of_arithmetic_rows
      h f lambda hlambda
  globalCertificate_eq_common := rfl
  restrictedCertificate_eq_common := rfl

def global_component_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    GlobalComponent.GlobalQWPsiFormulaComponent W f f lambda :=
  h.global

def restricted_component_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    RestrictedComponent.RestrictedQWLambdaFormulaComponent W f lambda :=
  h.restricted

theorem global_restricted_certificate_eq_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    h.global.finitePrimeSumReadOff.certificate =
      h.restricted.finitePrimeSumReadOff.certificate :=
  h.globalCertificate_eq_common.trans h.restrictedCertificate_eq_common.symm

theorem global_restricted_atoms_eq_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    h.global.finitePrimeSumReadOff.certificate.atoms =
      h.restricted.finitePrimeSumReadOff.certificate.atoms := by
  rw [global_restricted_certificate_eq_of_formula_components h]

theorem global_certificate_eq_common_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    h.global.finitePrimeSumReadOff.certificate = h.commonCertificate :=
  h.globalCertificate_eq_common

theorem restricted_certificate_eq_common_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    h.restricted.finitePrimeSumReadOff.certificate = h.commonCertificate :=
  h.restrictedCertificate_eq_common

theorem common_certificate_source_test_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    h.commonCertificate.support.sourceTest = h.sourceTest :=
  h.commonCertificateSourceTest

theorem global_certificate_source_test_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    h.global.finitePrimeSumReadOff.certificate.support.sourceTest =
      h.sourceTest := by
  rw [global_certificate_eq_common_of_formula_components h]
  exact common_certificate_source_test_of_formula_components h

theorem restricted_certificate_source_test_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    h.restricted.finitePrimeSumReadOff.certificate.support.sourceTest =
      h.sourceTest := by
  rw [restricted_certificate_eq_common_of_formula_components h]
  exact common_certificate_source_test_of_formula_components h

theorem qw_definition_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    W.qw f f = W.psi (W.convolutionStar f f) :=
  GlobalComponent.qw_definition_of_component h.global

theorem psi_sign_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          ∑ n ∈ W.globalPrimeIndexSet,
            W.finitePrimeTerm n (W.convolutionStar f f) :=
  GlobalComponent.psi_sign_of_component h.global

theorem psi_source_evaluator_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
            W f f h.global.finitePrimeSumReadOff.certificate.atoms :=
  GlobalComponent.psi_source_evaluator_of_component h.global

theorem qw_source_evaluator_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    W.qw f f =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
            W f f h.global.finitePrimeSumReadOff.certificate.atoms :=
  GlobalComponent.qw_source_evaluator_of_component h.global

theorem qw_lambda_formula_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          ∑ n ∈ W.restrictedPrimeIndexSet lambda,
            W.vonMangoldtWeight n * W.primePowerPairing n f f :=
  RestrictedComponent.qw_lambda_formula_of_component h.restricted

theorem qw_lambda_formula_source_evaluator_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
            W f f lambda h.restricted.finitePrimeSumReadOff.certificate.atoms :=
  RestrictedComponent.qw_lambda_formula_source_evaluator_of_component
    h.restricted

theorem global_finite_prime_sum_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f f h.global.finitePrimeSumReadOff.certificate.atoms :=
  GlobalComponent.global_finite_prime_sum_of_component h.global

theorem global_von_mangoldt_pairing_sum_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f f h.global.finitePrimeSumReadOff.certificate.atoms :=
  GlobalComponent.global_von_mangoldt_pairing_sum_of_component h.global

theorem restricted_finite_prime_sum_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f f lambda h.restricted.finitePrimeSumReadOff.certificate.atoms :=
  RestrictedComponent.restricted_finite_prime_sum_of_component h.restricted

theorem restricted_von_mangoldt_pairing_sum_of_formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25FormulaComponents W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f f lambda h.restricted.finitePrimeSumReadOff.certificate.atoms :=
  RestrictedComponent.restricted_von_mangoldt_pairing_sum_of_component
    h.restricted

end FormulaComponents
end CCM25Concrete
end Source
end ConnesWeilRH
