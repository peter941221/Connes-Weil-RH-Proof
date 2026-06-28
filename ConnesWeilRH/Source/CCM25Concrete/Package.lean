/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FormulaComponents

/-!
# CCM25 arithmetic package

This module binds the broad `CCM25Interface` and the fixed-test formula
components to the same concrete arithmetic rows.  The package stores only the
source rows and the fixed cutoff proof; all downstream objects are computed
from those fields so they cannot be overridden with data from a different row
set.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace Package

structure ConcreteCCM25ArithmeticPackage
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ) where
  rows : Interface.ConcreteCCM25ArithmeticRows W
  oneLtLambda : 1 < lambda

def ccm25_interface
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    CCM25Interface :=
  Interface.ccm25_interface_of_arithmetic_rows h.rows

def formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    FormulaComponents.ConcreteCCM25FormulaComponents W f lambda :=
  FormulaComponents.formula_components_of_arithmetic_rows
    h.rows f lambda h.oneLtLambda

theorem finite_prime_normalization_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  (ccm25_interface h).finitePrimeNormalization

theorem qw_definition_of_package_interface
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    WeilFormSymbols.QWDefinitionStatement W :=
  (ccm25_interface h).qwDefinition.1

theorem psi_sign_of_package_interface
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    WeilFormSymbols.PsiSignStatement W :=
  (ccm25_interface h).qwDefinition.2

theorem qw_lambda_formula_of_package_interface
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    WeilFormSymbols.QWLambdaFormulaStatement W :=
  (ccm25_interface h).qwLambdaFormula

theorem pole_normalization_of_package_interface
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    WeilFormSymbols.PoleNormalizationStatement W :=
  (ccm25_interface h).poleNormalization

theorem qw_definition_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qw f f = W.psi (W.convolutionStar f f) :=
  FormulaComponents.qw_definition_of_formula_components
    (formula_components h)

theorem psi_sign_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          ∑ n ∈ W.globalPrimeIndexSet,
            W.finitePrimeTerm n (W.convolutionStar f f) :=
  FormulaComponents.psi_sign_of_formula_components
    (formula_components h)

theorem qw_lambda_formula_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          ∑ n ∈ W.restrictedPrimeIndexSet lambda,
            W.vonMangoldtWeight n * W.primePowerPairing n f f :=
  FormulaComponents.qw_lambda_formula_of_formula_components
    (formula_components h)

theorem global_finite_prime_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f f (formula_components h).global.finitePrimeSumReadOff.certificate.atoms :=
  FormulaComponents.global_finite_prime_sum_of_formula_components
    (formula_components h)

theorem restricted_finite_prime_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f f lambda
        (formula_components h).restricted.finitePrimeSumReadOff.certificate.atoms :=
  FormulaComponents.restricted_finite_prime_sum_of_formula_components
    (formula_components h)

end Package
end CCM25Concrete
end Source
end ConnesWeilRH
