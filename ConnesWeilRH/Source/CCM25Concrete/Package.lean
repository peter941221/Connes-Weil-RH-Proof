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

noncomputable def ccm25_interface
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    CCM25Interface :=
  Interface.ccm25_interface_of_arithmetic_rows h.rows

noncomputable def formula_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    FormulaComponents.ConcreteCCM25FormulaComponents W f lambda :=
  FormulaComponents.formula_components_of_arithmetic_rows
    h.rows f lambda h.oneLtLambda

def source_test_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    PrimePowerTest.SourceTestEvaluationInterface W f f :=
  Interface.source_test_of_arithmetic_rows h.rows f f

theorem global_restricted_certificate_eq_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (formula_components h).global.finitePrimeSumReadOff.certificate =
      (formula_components h).restricted.finitePrimeSumReadOff.certificate :=
  FormulaComponents.global_restricted_certificate_eq_of_formula_components
    (formula_components h)

theorem global_restricted_atoms_eq_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (formula_components h).global.finitePrimeSumReadOff.certificate.atoms =
      (formula_components h).restricted.finitePrimeSumReadOff.certificate.atoms :=
  FormulaComponents.global_restricted_atoms_eq_of_formula_components
    (formula_components h)

theorem global_concrete_object_certificate_eq_common_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (GlobalComponent.global_concrete_object_of_component
      (formula_components h).global).certificate =
      (formula_components h).commonCertificate :=
  FormulaComponents.global_concrete_object_certificate_eq_common_of_formula_components
    (formula_components h)

theorem restricted_concrete_object_certificate_eq_common_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (RestrictedComponent.restricted_concrete_object_of_component
      (formula_components h).restricted).certificate =
      (formula_components h).commonCertificate :=
  FormulaComponents.restricted_concrete_object_certificate_eq_common_of_formula_components
    (formula_components h)

theorem global_restricted_concrete_object_certificate_eq_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (GlobalComponent.global_concrete_object_of_component
      (formula_components h).global).certificate =
      (RestrictedComponent.restricted_concrete_object_of_component
        (formula_components h).restricted).certificate :=
  FormulaComponents.global_restricted_concrete_object_certificate_eq_of_formula_components
    (formula_components h)

noncomputable def common_concrete_object_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      W f f lambda :=
  FormulaComponents.common_concrete_object_of_formula_components
    (formula_components h)

theorem common_concrete_object_certificate_eq_common_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (common_concrete_object_of_package h).certificate =
      (formula_components h).commonCertificate :=
  FormulaComponents.common_concrete_object_certificate_eq_common_of_formula_components
    (formula_components h)

theorem global_concrete_object_eq_common_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    GlobalComponent.global_concrete_object_of_component
        (formula_components h).global =
      common_concrete_object_of_package h :=
  FormulaComponents.global_concrete_object_eq_common_of_formula_components
    (formula_components h)

theorem restricted_concrete_object_eq_common_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    RestrictedComponent.restricted_concrete_object_of_component
        (formula_components h).restricted =
      common_concrete_object_of_package h :=
  FormulaComponents.restricted_concrete_object_eq_common_of_formula_components
    (formula_components h)

theorem global_restricted_concrete_object_eq_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    GlobalComponent.global_concrete_object_of_component
        (formula_components h).global =
      RestrictedComponent.restricted_concrete_object_of_component
        (formula_components h).restricted :=
  FormulaComponents.global_restricted_concrete_object_eq_of_formula_components
    (formula_components h)

theorem finite_prime_normalization_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  (ccm25_interface h).finitePrimeNormalization

theorem qw_definition_of_package_interface
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    WeilFormSymbols.QWDefinitionStatement W :=
  (ccm25_interface h).qwDefinition

theorem psi_sign_of_package_interface
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    WeilFormSymbols.PsiSignStatement W :=
  (ccm25_interface h).psiSign

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

theorem psi_source_evaluator_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let comps := formula_components h
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
            W f f comps.global.finitePrimeSumReadOff.certificate.atoms :=
  FormulaComponents.psi_source_evaluator_of_formula_components
    (formula_components h)

theorem qw_source_evaluator_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let comps := formula_components h
    W.qw f f =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
            W f f comps.global.finitePrimeSumReadOff.certificate.atoms :=
  FormulaComponents.qw_source_evaluator_of_formula_components
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

theorem qw_lambda_formula_source_evaluator_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let comps := formula_components h
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
            W f f lambda
              comps.restricted.finitePrimeSumReadOff.certificate.atoms :=
  FormulaComponents.qw_lambda_formula_source_evaluator_of_formula_components
    (formula_components h)

theorem psi_scoped_source_evaluator_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let comps := formula_components h
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
            W f f comps.global.finitePrimeSumReadOff.scopedArithmeticData :=
  FormulaComponents.psi_scoped_source_evaluator_of_formula_components
    (formula_components h)

theorem qw_scoped_source_evaluator_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let comps := formula_components h
    W.qw f f =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
            W f f comps.global.finitePrimeSumReadOff.scopedArithmeticData :=
  FormulaComponents.qw_scoped_source_evaluator_of_formula_components
    (formula_components h)

theorem qw_lambda_formula_scoped_source_evaluator_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let comps := formula_components h
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
            W f f lambda
              comps.restricted.finitePrimeSumReadOff.scopedArithmeticData :=
  FormulaComponents.qw_lambda_formula_scoped_source_evaluator_of_formula_components
    (formula_components h)

noncomputable def source_global_finite_prime_evaluator_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum W f f
    (formula_components h).global.finitePrimeSumReadOff.certificate.atoms

noncomputable def source_restricted_finite_prime_evaluator_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum W f f lambda
    (formula_components h).restricted.finitePrimeSumReadOff.certificate.atoms

noncomputable def source_common_global_finite_prime_evaluator_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum W f f
    (formula_components h).commonCertificate.atoms

noncomputable def source_common_restricted_finite_prime_evaluator_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum W f f lambda
    (formula_components h).commonCertificate.atoms

noncomputable def source_global_finite_prime_evaluator_scoped_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet W f f
    (formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData

noncomputable def source_restricted_finite_prime_evaluator_scoped_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
    W f f lambda
      (formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData

noncomputable def source_common_global_finite_prime_evaluator_scoped_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet W f f
    (FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
      (formula_components h).commonCertificate)

noncomputable def source_common_restricted_finite_prime_evaluator_scoped_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
    W f f lambda
      (FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
        (formula_components h).commonCertificate)

theorem source_global_sum_eq_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_global_finite_prime_evaluator_sum h =
      source_common_global_finite_prime_evaluator_sum h := by
  dsimp [source_global_finite_prime_evaluator_sum,
    source_common_global_finite_prime_evaluator_sum]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem source_restricted_sum_eq_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_restricted_finite_prime_evaluator_sum h =
      source_common_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_restricted_finite_prime_evaluator_sum,
    source_common_restricted_finite_prime_evaluator_sum]
  rw [FormulaComponents.restricted_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem source_global_scoped_sum_eq_common_scoped_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_global_finite_prime_evaluator_scoped_sum h =
      source_common_global_finite_prime_evaluator_scoped_sum h := by
  dsimp [source_global_finite_prime_evaluator_scoped_sum,
    source_common_global_finite_prime_evaluator_scoped_sum]
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem source_restricted_scoped_sum_eq_common_scoped_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_restricted_finite_prime_evaluator_scoped_sum h =
      source_common_restricted_finite_prime_evaluator_scoped_sum h := by
  dsimp [source_restricted_finite_prime_evaluator_scoped_sum,
    source_common_restricted_finite_prime_evaluator_scoped_sum]
  rw [(formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.restricted_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem source_common_restricted_scoped_sum_eq_common_global_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_common_restricted_finite_prime_evaluator_scoped_sum h =
      source_common_global_finite_prime_evaluator_scoped_sum h := by
  dsimp [source_common_restricted_finite_prime_evaluator_scoped_sum,
    source_common_global_finite_prime_evaluator_scoped_sum,
    PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet,
    PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet,
    PrimePowerArithmetic.SourceFinitePrimeEvaluatorSumOnIndexSet,
    FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate,
    FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate]
  rw [FinitePrimeCertificate.restricted_index_set_eq_global_of_arithmetic_certificate
    (h := (formula_components h).commonCertificate)]

theorem source_restricted_scoped_sum_eq_global_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_restricted_finite_prime_evaluator_scoped_sum h =
      source_global_finite_prime_evaluator_scoped_sum h := by
  rw [source_restricted_scoped_sum_eq_common_scoped_atoms_of_package h,
    source_common_restricted_scoped_sum_eq_common_global_of_package h,
    source_global_scoped_sum_eq_common_scoped_atoms_of_package h]

theorem source_common_global_scoped_sum_eq_common_global_sum_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_common_global_finite_prime_evaluator_scoped_sum h =
      source_common_global_finite_prime_evaluator_sum h := by
  dsimp [source_common_global_finite_prime_evaluator_scoped_sum,
    source_common_global_finite_prime_evaluator_sum]
  exact
    FinitePrimeCertificate.arithmetic_global_scoped_sum_eq_global_sum_of_certificate
      (formula_components h).commonCertificate

theorem source_common_restricted_scoped_sum_eq_common_restricted_sum_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_common_restricted_finite_prime_evaluator_scoped_sum h =
      source_common_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_common_restricted_finite_prime_evaluator_scoped_sum,
    source_common_restricted_finite_prime_evaluator_sum]
  exact
    FinitePrimeCertificate.arithmetic_restricted_scoped_sum_eq_restricted_sum_of_certificate
      (formula_components h).commonCertificate

theorem source_global_scoped_sum_eq_global_sum_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_global_finite_prime_evaluator_scoped_sum h =
      source_global_finite_prime_evaluator_sum h := by
  rw [source_global_scoped_sum_eq_common_scoped_atoms_of_package h,
    source_common_global_scoped_sum_eq_common_global_sum_of_package h,
    ← source_global_sum_eq_common_atoms_of_package h]

theorem source_restricted_scoped_sum_eq_restricted_sum_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_restricted_finite_prime_evaluator_scoped_sum h =
      source_restricted_finite_prime_evaluator_sum h := by
  rw [source_restricted_scoped_sum_eq_common_scoped_atoms_of_package h,
    source_common_restricted_scoped_sum_eq_common_restricted_sum_of_package h,
    ← source_restricted_sum_eq_common_atoms_of_package h]

theorem psi_source_evaluator_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          source_common_global_finite_prime_evaluator_sum h := by
  rw [psi_source_evaluator_of_package_components h]
  dsimp [source_common_global_finite_prime_evaluator_sum]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem qw_source_evaluator_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qw f f =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          source_common_global_finite_prime_evaluator_sum h := by
  rw [qw_source_evaluator_of_package_components h]
  dsimp [source_common_global_finite_prime_evaluator_sum]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem qw_lambda_formula_source_evaluator_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          source_common_restricted_finite_prime_evaluator_sum h := by
  rw [qw_lambda_formula_source_evaluator_of_package_components h]
  dsimp [source_common_restricted_finite_prime_evaluator_sum]
  rw [FormulaComponents.restricted_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem psi_scoped_source_evaluator_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          source_common_global_finite_prime_evaluator_scoped_sum h := by
  rw [psi_scoped_source_evaluator_of_package_components h]
  dsimp [source_common_global_finite_prime_evaluator_scoped_sum]
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem qw_scoped_source_evaluator_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qw f f =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          source_common_global_finite_prime_evaluator_scoped_sum h := by
  rw [qw_scoped_source_evaluator_of_package_components h]
  dsimp [source_common_global_finite_prime_evaluator_scoped_sum]
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem qw_lambda_formula_scoped_source_evaluator_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          source_common_restricted_finite_prime_evaluator_scoped_sum h := by
  rw [qw_lambda_formula_scoped_source_evaluator_of_package_components h]
  dsimp [source_common_restricted_finite_prime_evaluator_scoped_sum]
  rw [(formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.restricted_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem common_atom_archimedean_contribution_matches_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (hbalance :
      W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_restricted_finite_prime_evaluator_sum h =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_global_finite_prime_evaluator_sum h) :
    W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          source_common_restricted_finite_prime_evaluator_sum h =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          source_common_global_finite_prime_evaluator_sum h := by
  rw [← source_restricted_sum_eq_common_atoms_of_package h,
    ← source_global_sum_eq_common_atoms_of_package h]
  exact hbalance

theorem qw_lambda_eq_qw_of_common_atom_archimedean_contribution
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (hbalance :
      W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_common_restricted_finite_prime_evaluator_sum h =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_common_global_finite_prime_evaluator_sum h) :
    W.qwLambda lambda f f = W.qw f f := by
  calc
    W.qwLambda lambda f f =
        W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_common_restricted_finite_prime_evaluator_sum h :=
      qw_lambda_formula_source_evaluator_common_atoms_of_package h
    _ =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_common_global_finite_prime_evaluator_sum h :=
      hbalance
    _ = W.qw f f :=
      (qw_source_evaluator_common_atoms_of_package h).symm

theorem qw_lambda_eq_qw_of_archimedean_contribution
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (hbalance :
      W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_restricted_finite_prime_evaluator_sum h =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_global_finite_prime_evaluator_sum h) :
    W.qwLambda lambda f f = W.qw f f :=
  qw_lambda_eq_qw_of_common_atom_archimedean_contribution h
    (common_atom_archimedean_contribution_matches_of_package h hbalance)

theorem source_global_sum_uses_restricted_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_global_finite_prime_evaluator_sum h =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum W f f
        (formula_components h).restricted.finitePrimeSumReadOff.certificate.atoms := by
  dsimp [source_global_finite_prime_evaluator_sum]
  rw [global_restricted_atoms_eq_of_package h]

theorem source_restricted_sum_uses_global_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_restricted_finite_prime_evaluator_sum h =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum W f f lambda
        (formula_components h).global.finitePrimeSumReadOff.certificate.atoms := by
  dsimp [source_restricted_finite_prime_evaluator_sum]
  rw [← global_restricted_atoms_eq_of_package h]

theorem global_finite_prime_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_global_finite_prime_evaluator_sum h :=
  FormulaComponents.global_finite_prime_sum_of_formula_components
    (formula_components h)

theorem global_finite_prime_scoped_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_global_finite_prime_evaluator_scoped_sum h := by
  dsimp [source_global_finite_prime_evaluator_scoped_sum]
  exact
    FormulaComponents.global_finite_prime_scoped_sum_of_formula_components
      (formula_components h)

theorem global_finite_prime_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_global_finite_prime_evaluator_sum h := by
  rw [global_finite_prime_sum_of_package_components h,
    source_global_sum_eq_common_atoms_of_package h]

theorem global_finite_prime_scoped_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_global_finite_prime_evaluator_scoped_sum h := by
  rw [global_finite_prime_scoped_sum_of_package_components h,
    source_global_scoped_sum_eq_common_scoped_atoms_of_package h]

theorem global_von_mangoldt_pairing_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_global_finite_prime_evaluator_sum h :=
  FormulaComponents.global_von_mangoldt_pairing_sum_of_formula_components
    (formula_components h)

theorem global_von_mangoldt_pairing_scoped_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_global_finite_prime_evaluator_scoped_sum h := by
  dsimp [source_global_finite_prime_evaluator_scoped_sum]
  exact
    FormulaComponents.global_von_mangoldt_pairing_scoped_sum_of_formula_components
      (formula_components h)

theorem global_von_mangoldt_pairing_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_global_finite_prime_evaluator_sum h := by
  rw [global_von_mangoldt_pairing_sum_of_package_components h,
    source_global_sum_eq_common_atoms_of_package h]

theorem global_von_mangoldt_pairing_scoped_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_global_finite_prime_evaluator_scoped_sum h := by
  rw [global_von_mangoldt_pairing_scoped_sum_of_package_components h,
    source_global_scoped_sum_eq_common_scoped_atoms_of_package h]

theorem restricted_finite_prime_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_restricted_finite_prime_evaluator_sum h :=
  FormulaComponents.restricted_finite_prime_sum_of_formula_components
    (formula_components h)

theorem restricted_finite_prime_scoped_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_restricted_finite_prime_evaluator_scoped_sum h := by
  dsimp [source_restricted_finite_prime_evaluator_scoped_sum]
  exact
    FormulaComponents.restricted_finite_prime_scoped_sum_of_formula_components
      (formula_components h)

theorem restricted_finite_prime_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_restricted_finite_prime_evaluator_sum h := by
  rw [restricted_finite_prime_sum_of_package_components h,
    source_restricted_sum_eq_common_atoms_of_package h]

theorem restricted_finite_prime_scoped_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_restricted_finite_prime_evaluator_scoped_sum h := by
  rw [restricted_finite_prime_scoped_sum_of_package_components h,
    source_restricted_scoped_sum_eq_common_scoped_atoms_of_package h]

theorem restricted_index_set_eq_global_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.restrictedPrimeIndexSet lambda = W.globalPrimeIndexSet :=
  FinitePrimeCertificate.restricted_index_set_eq_global_of_arithmetic_certificate
    (formula_components h).commonCertificate

noncomputable def exact_support_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f f lambda :=
  FinitePrimeCertificate.exact_support_of_arithmetic_certificate
    (formula_components h).commonCertificate

noncomputable def finite_prime_concrete_object_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      W f f lambda :=
  FinitePrimeCertificate.concrete_object_of_arithmetic_certificate
    (formula_components h).commonCertificate

theorem finite_prime_concrete_object_certificate_eq_common
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (finite_prime_concrete_object_of_package h).certificate =
      (formula_components h).commonCertificate :=
  rfl

theorem exact_support_eq_concrete_object_exact_support
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    exact_support_of_package h =
      (finite_prime_concrete_object_of_package h).exactSupport :=
  rfl

theorem finite_prime_concrete_object_weight_read_off
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (n : ℕ) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  FinitePrimeCertificate.concrete_object_weight_eq_mathlib
    (finite_prime_concrete_object_of_package h) n

theorem finite_prime_concrete_object_weight_eq_mathlib
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (n : ℕ) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  finite_prime_concrete_object_weight_read_off h n

theorem finite_prime_concrete_object_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (n : ℕ) :
    let obj := finite_prime_concrete_object_of_package h
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        ((obj.atomData n).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f f) (n : ℝ) +
          (obj.atomData n).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f f) ((n : ℝ)⁻¹)) :=
  FinitePrimeCertificate.concrete_object_pairing_formula_source_evaluator
    (finite_prime_concrete_object_of_package h) n

theorem finite_prime_concrete_object_term_formula_mathlib_pairing
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f f :=
  FinitePrimeCertificate.concrete_object_term_formula_mathlib_pairing
    (finite_prime_concrete_object_of_package h) n

theorem finite_prime_concrete_object_global_sum_read_off
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_global_finite_prime_evaluator_sum h := by
  dsimp [source_common_global_finite_prime_evaluator_sum]
  exact
    FinitePrimeCertificate.concrete_object_global_finite_prime_term_sum_read_off
      (finite_prime_concrete_object_of_package h)

theorem finite_prime_concrete_object_restricted_sum_read_off
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_common_restricted_finite_prime_evaluator_sum]
  exact
    FinitePrimeCertificate.concrete_object_restricted_finite_prime_term_sum_read_off
      (finite_prime_concrete_object_of_package h)

theorem finite_prime_concrete_object_global_pairing_sum_read_off
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_global_finite_prime_evaluator_sum h := by
  dsimp [source_common_global_finite_prime_evaluator_sum]
  exact
    FinitePrimeCertificate.concrete_object_global_von_mangoldt_pairing_sum_read_off
      (finite_prime_concrete_object_of_package h)

theorem finite_prime_concrete_object_restricted_pairing_sum_read_off
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_common_restricted_finite_prime_evaluator_sum]
  exact
    FinitePrimeCertificate.concrete_object_restricted_von_mangoldt_pairing_sum_read_off
      (finite_prime_concrete_object_of_package h)

theorem exact_support_uses_common_certificate_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    exact_support_of_package h =
      FinitePrimeCertificate.exact_support_of_arithmetic_certificate
        (formula_components h).commonCertificate := by
  rfl

theorem visibility_at_lambda_of_package_exact_support
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    FinitePrimeExact.FinitePrimeVisibilityAtLambdaStatement W f f lambda :=
  FinitePrimeExact.visibility_at_lambda_of_exact_support
    (exact_support_of_package h)

theorem global_exact_of_package_exact_support
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        (exact_support_of_package h).sourcePrimePowerIndex n ∧
          (exact_support_of_package h).sourceAtomVisible n :=
  (exact_support_of_package h).globalExact

theorem restricted_exact_of_package_exact_support
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        (exact_support_of_package h).sourcePrimePowerIndex n ∧
          (exact_support_of_package h).sourceAtomVisible n ∧
            (exact_support_of_package h).sourceInLambdaCut n :=
  (exact_support_of_package h).restrictedExact

theorem visible_atoms_in_lambda_cut_of_package_exact_support
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f f) →
        (exact_support_of_package h).sourceInLambdaCut n :=
  (exact_support_of_package h).visibleAtomsInLambdaCut

theorem source_restricted_finite_prime_evaluator_sum_eq_global
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_restricted_finite_prime_evaluator_sum h =
      source_global_finite_prime_evaluator_sum h := by
  rw [source_restricted_sum_uses_global_atoms_of_package h,
    source_global_sum_uses_restricted_atoms_of_package h]
  dsimp [
    PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum,
    PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum]
  rw [restricted_index_set_eq_global_of_package h]
  rw [global_restricted_atoms_eq_of_package h]

theorem source_common_restricted_sum_eq_common_global_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_common_restricted_finite_prime_evaluator_sum h =
      source_common_global_finite_prime_evaluator_sum h := by
  rw [← source_restricted_sum_eq_common_atoms_of_package h,
    source_restricted_finite_prime_evaluator_sum_eq_global h,
    source_global_sum_eq_common_atoms_of_package h]

theorem restricted_von_mangoldt_pairing_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_restricted_finite_prime_evaluator_sum h :=
  FormulaComponents.restricted_von_mangoldt_pairing_sum_of_formula_components
    (formula_components h)

theorem restricted_von_mangoldt_pairing_scoped_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_restricted_finite_prime_evaluator_scoped_sum h := by
  dsimp [source_restricted_finite_prime_evaluator_scoped_sum]
  exact
    FormulaComponents.restricted_von_mangoldt_pairing_scoped_sum_of_formula_components
      (formula_components h)

theorem restricted_von_mangoldt_pairing_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_restricted_finite_prime_evaluator_sum h := by
  rw [restricted_von_mangoldt_pairing_sum_of_package_components h,
    source_restricted_sum_eq_common_atoms_of_package h]

theorem restricted_von_mangoldt_pairing_scoped_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_restricted_finite_prime_evaluator_scoped_sum h := by
  rw [restricted_von_mangoldt_pairing_scoped_sum_of_package_components h,
    source_restricted_scoped_sum_eq_common_scoped_atoms_of_package h]

theorem formula_components_source_test_eq_package_source_test
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (formula_components h).sourceTest = source_test_of_package h :=
  rfl

theorem common_certificate_source_test_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (formula_components h).commonCertificate.support.sourceTest =
      source_test_of_package h := by
  rw [
    FormulaComponents.common_certificate_source_test_of_formula_components
      (formula_components h),
    formula_components_source_test_eq_package_source_test h]

theorem finite_prime_concrete_object_source_test_eq_package_source_test
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (finite_prime_concrete_object_of_package h).sourceTest =
      source_test_of_package h := by
  dsimp [finite_prime_concrete_object_of_package]
  exact common_certificate_source_test_of_package h

theorem finite_prime_concrete_object_global_index_source_data
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerSupport.SourceGlobalIndexData
      PrimePowerArithmetic.SourcePrimePowerIndex
      (source_test_of_package h).sourceAtomVisible n := by
  have hdata :=
    (finite_prime_concrete_object_of_package h).globalIndexData hn
  simpa [finite_prime_concrete_object_source_test_eq_package_source_test h]
    using hdata

theorem finite_prime_concrete_object_global_index_route_visible
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeAtomVisible n (W.convolutionStar f f) := by
  have hvisible :
      (finite_prime_concrete_object_of_package h).sourceTest.sourceAtomVisible
        n :=
    FinitePrimeCertificate.concrete_object_global_index_visible
      (finite_prime_concrete_object_of_package h) hn
  have hsource :
      (source_test_of_package h).sourceAtomVisible n := by
    simpa [finite_prime_concrete_object_source_test_eq_package_source_test h]
      using hvisible
  exact (PrimePowerTest.route_visibility_iff_source_visibility
    (source_test_of_package h) n).2 hsource

theorem finite_prime_concrete_object_restricted_index_source_data
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceRestrictedIndexData
      PrimePowerArithmetic.SourcePrimePowerIndex
      (source_test_of_package h).sourceAtomVisible lambda n := by
  have hdata :=
    (finite_prime_concrete_object_of_package h).restrictedIndexData hn
  simpa [finite_prime_concrete_object_source_test_eq_package_source_test h]
    using hdata

theorem finite_prime_concrete_object_restricted_index_route_visible
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeAtomVisible n (W.convolutionStar f f) := by
  have hvisible :
      (finite_prime_concrete_object_of_package h).sourceTest.sourceAtomVisible
        n :=
    FinitePrimeCertificate.concrete_object_restricted_index_visible
      (finite_prime_concrete_object_of_package h) hn
  have hsource :
      (source_test_of_package h).sourceAtomVisible n := by
    simpa [finite_prime_concrete_object_source_test_eq_package_source_test h]
      using hvisible
  exact (PrimePowerTest.route_visibility_iff_source_visibility
    (source_test_of_package h) n).2 hsource

theorem common_certificate_route_visible_atom_data_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ}
    (hvisible :
      W.finitePrimeAtomVisible n (W.convolutionStar f f)) :
    PrimePowerSupport.SourceVisibleAtomData
      IsPrimePow
      (fun n => W.finitePrimeAtomVisible n (W.convolutionStar f f)) n := by
  let hcert := (formula_components h).commonCertificate
  let hsource :=
    (FinitePrimeCertificate.visible_iff_of_certificate
      (FinitePrimeCertificate.certificate_of_arithmetic_certificate hcert) n).1
      hvisible
  have hprime : PrimePowerArithmetic.SourcePrimePowerIndex n := by
    simpa [
      FinitePrimeCertificate.certificate_of_arithmetic_certificate,
      FinitePrimeCertificate.atom_certificate_of_arithmetic_certificate,
      PrimePowerSupport.support_skeleton_of_arithmetic_support_skeleton]
      using hsource.primePowerIndex
  exact
    { primePowerIndex :=
        PrimePowerArithmetic.source_prime_power_index_iff_mathlib.1
          hprime
      atomVisible := hvisible }

theorem finite_prime_concrete_object_global_index_route_data
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerSupport.SourceGlobalIndexData
      IsPrimePow
      (fun n => W.finitePrimeAtomVisible n (W.convolutionStar f f)) n where
  primePowerIndex :=
    (common_certificate_route_visible_atom_data_of_package h
      (finite_prime_concrete_object_global_index_route_visible h hn)).primePowerIndex
  atomVisible :=
    (common_certificate_route_visible_atom_data_of_package h
      (finite_prime_concrete_object_global_index_route_visible h hn)).atomVisible

theorem finite_prime_concrete_object_restricted_index_route_data
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceRestrictedIndexData
      IsPrimePow
      (fun n => W.finitePrimeAtomVisible n (W.convolutionStar f f))
      lambda n where
  primePowerIndex :=
    (common_certificate_route_visible_atom_data_of_package h
      (finite_prime_concrete_object_restricted_index_route_visible h hn)).primePowerIndex
  atomVisible :=
    (common_certificate_route_visible_atom_data_of_package h
      (finite_prime_concrete_object_restricted_index_route_visible h hn)).atomVisible
  lambdaCut :=
    FinitePrimeCertificate.concrete_object_restricted_index_lambda_cut
      (finite_prime_concrete_object_of_package h) hn

theorem exact_support_source_test_eq_package_source_test
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (exact_support_of_package h).sourceAtomVisible =
      (source_test_of_package h).sourceAtomVisible := by
  funext n
  dsimp [exact_support_of_package]
  dsimp [
    FinitePrimeCertificate.exact_support_of_arithmetic_certificate,
    FinitePrimeCertificate.exact_support_of_certificate,
    FinitePrimeCertificate.certificate_of_arithmetic_certificate,
    FinitePrimeCertificate.certificate_of_atom_certificate,
    FinitePrimeCertificate.atom_certificate_of_arithmetic_certificate,
    FinitePrimeCertificate.source_prime_power_support_of_certificate,
    PrimePowerSupport.exact_support_of_source_prime_power_support,
    PrimePowerSupport.source_prime_power_support_of_skeleton,
    PrimePowerSupport.support_skeleton_of_arithmetic_support_skeleton]
  rw [common_certificate_source_test_of_package h]

theorem global_certificate_source_test_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (formula_components h).global.finitePrimeSumReadOff.certificate.support.sourceTest =
      source_test_of_package h := by
  rw [
    FormulaComponents.global_certificate_source_test_of_formula_components
      (formula_components h),
    formula_components_source_test_eq_package_source_test h]

theorem restricted_certificate_source_test_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (formula_components h).restricted.finitePrimeSumReadOff.certificate.support.sourceTest =
      source_test_of_package h := by
  rw [
    FormulaComponents.restricted_certificate_source_test_of_formula_components
      (formula_components h),
    formula_components_source_test_eq_package_source_test h]

theorem common_certificate_global_index_source_data_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerSupport.SourceGlobalIndexData
      PrimePowerArithmetic.SourcePrimePowerIndex
      (source_test_of_package h).sourceAtomVisible n := by
  exact finite_prime_concrete_object_global_index_source_data h hn

theorem common_certificate_global_index_prime_power_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  (finite_prime_concrete_object_global_index_route_data h hn).primePowerIndex

theorem common_certificate_global_index_visible_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeAtomVisible n (W.convolutionStar f f) :=
  (finite_prime_concrete_object_global_index_route_data h hn).atomVisible

theorem common_certificate_restricted_index_source_data_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceRestrictedIndexData
      PrimePowerArithmetic.SourcePrimePowerIndex
      (source_test_of_package h).sourceAtomVisible lambda n := by
  exact finite_prime_concrete_object_restricted_index_source_data h hn

theorem common_certificate_restricted_index_prime_power_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  (finite_prime_concrete_object_restricted_index_route_data h hn).primePowerIndex

theorem common_certificate_restricted_index_visible_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeAtomVisible n (W.convolutionStar f f) :=
  (finite_prime_concrete_object_restricted_index_route_data h hn).atomVisible

theorem common_certificate_restricted_index_lambda_cut_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceLambdaCut lambda n :=
  (finite_prime_concrete_object_restricted_index_route_data h hn).lambdaCut

theorem global_index_prime_power_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  common_certificate_global_index_prime_power_of_package h hn

theorem global_index_visible_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeAtomVisible n (W.convolutionStar f f) :=
  common_certificate_global_index_visible_of_package h hn

theorem global_index_one_lt_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    1 < n :=
  IsPrimePow.one_lt (global_index_prime_power_of_package h hn)

theorem global_index_weight_read_off_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.globalPrimeIndexSet) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  finite_prime_concrete_object_weight_eq_mathlib h n

theorem global_index_pairing_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.globalPrimeIndexSet) :
    let atom := (formula_components h).commonCertificate.atoms.atIndex n
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f f) (n : ℝ) +
          atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f f) ((n : ℝ)⁻¹)) :=
  PrimePowerPairing.source_prime_power_pairing_formula_source_evaluator
    ((formula_components h).commonCertificate.atoms.atIndex n).sourcePairing

theorem global_index_finite_prime_term_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f f :=
  PrimePowerArithmetic.source_finite_prime_term_formula_mathlib_pairing
    ((formula_components h).commonCertificate.atoms.atIndex n)

theorem restricted_index_prime_power_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  common_certificate_restricted_index_prime_power_of_package h hn

theorem restricted_index_visible_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeAtomVisible n (W.convolutionStar f f) :=
  common_certificate_restricted_index_visible_of_package h hn

theorem restricted_index_lambda_cut_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceLambdaCut lambda n :=
  common_certificate_restricted_index_lambda_cut_of_package h hn

theorem restricted_index_one_lt_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    1 < n :=
  PrimePowerSupport.source_lambda_cut_one_lt
    (restricted_index_lambda_cut_of_package h hn)

theorem restricted_index_le_lambda_sq_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  PrimePowerSupport.source_lambda_cut_le_lambda_sq
    (restricted_index_lambda_cut_of_package h hn)

theorem restricted_index_weight_read_off_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  finite_prime_concrete_object_weight_eq_mathlib h n

theorem restricted_index_pairing_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom := (formula_components h).commonCertificate.atoms.atIndex n
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f f) (n : ℝ) +
          atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f f) ((n : ℝ)⁻¹)) :=
  PrimePowerPairing.source_prime_power_pairing_formula_source_evaluator
    ((formula_components h).commonCertificate.atoms.atIndex n).sourcePairing

theorem restricted_index_finite_prime_term_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f f :=
  PrimePowerArithmetic.source_finite_prime_term_formula_mathlib_pairing
    ((formula_components h).commonCertificate.atoms.atIndex n)

end Package
end CCM25Concrete
end Source
end ConnesWeilRH
