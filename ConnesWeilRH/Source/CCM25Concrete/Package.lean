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

open FinitePrimeCertificate
open PrimePowerArithmetic

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
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            W f f comps.global.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [FormulaComponents.psi_scoped_source_evaluator_of_formula_components
    (formula_components h)]

theorem qw_source_evaluator_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let comps := formula_components h
    W.qw f f =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            W f f comps.global.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [FormulaComponents.qw_scoped_source_evaluator_of_formula_components
    (formula_components h)]

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
          PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
            W f f lambda
              comps.restricted.finitePrimeSumReadOff.scopedArithmeticData := by
  rw [FormulaComponents.qw_lambda_formula_scoped_source_evaluator_of_formula_components
    (formula_components h)]

theorem psi_scoped_source_evaluator_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let comps := formula_components h
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
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
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
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
          PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
            W f f lambda
              comps.restricted.finitePrimeSumReadOff.scopedArithmeticData :=
  FormulaComponents.qw_lambda_formula_scoped_source_evaluator_of_formula_components
    (formula_components h)

noncomputable def source_global_finite_prime_evaluator_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f f
    (formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData

noncomputable def source_restricted_finite_prime_evaluator_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
    W f f lambda
      (formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData

noncomputable def source_common_global_finite_prime_evaluator_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f f
    (FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
      (formula_components h).commonCertificate)

noncomputable def source_common_restricted_finite_prime_evaluator_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
    W f f lambda
      (FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
        (formula_components h).commonCertificate)

noncomputable def source_global_finite_prime_source_evaluations_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  GlobalComponent.GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
    W f f (formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData

noncomputable def source_restricted_finite_prime_source_evaluations_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  RestrictedComponent.RestrictedSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
    W f lambda
      (formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData

noncomputable def source_common_global_finite_prime_source_evaluations_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  GlobalComponent.GlobalSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
    W f f
      (FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
        (formula_components h).commonCertificate)

noncomputable def source_common_restricted_finite_prime_source_evaluations_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  RestrictedComponent.RestrictedSourceEvaluationsFinitePrimeEvaluatorSumOnIndexSet
    W f lambda
      (FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
        (formula_components h).commonCertificate)

noncomputable def source_global_finite_prime_evaluator_scoped_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f f
    (formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData

noncomputable def source_restricted_finite_prime_evaluator_scoped_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
    W f f lambda
      (formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData

noncomputable def source_common_global_finite_prime_evaluator_scoped_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f f
    (FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
      (formula_components h).commonCertificate)

noncomputable def source_common_restricted_finite_prime_evaluator_scoped_sum
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
    W f f lambda
      (FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
        (formula_components h).commonCertificate)

noncomputable def ScopedRestrictedArchimedeanFormula
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ)
    (pkg : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  W.archimedeanTerm (W.convolutionStar f f) +
      W.polePairing f -
        source_restricted_finite_prime_evaluator_scoped_sum pkg

noncomputable def ScopedGlobalArchimedeanFormula
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ)
    (pkg : ConcreteCCM25ArithmeticPackage W f lambda) : ℝ :=
  W.poleFunctional (W.convolutionStar f f) -
    W.archimedeanTerm (W.convolutionStar f f) -
      source_global_finite_prime_evaluator_scoped_sum pkg

def ScopedArchimedeanContributionBalance
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ)
    (pkg : ConcreteCCM25ArithmeticPackage W f lambda) : Prop :=
  ScopedRestrictedArchimedeanFormula W f lambda pkg =
    ScopedGlobalArchimedeanFormula W f lambda pkg

theorem qwLambda_eq_scopedRestrictedArchimedeanFormula_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (pkg : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qwLambda lambda f f =
      ScopedRestrictedArchimedeanFormula W f lambda pkg := by
  simpa [ScopedRestrictedArchimedeanFormula]
    using qw_lambda_formula_scoped_source_evaluator_of_package_components
      pkg

theorem scopedRestrictedArchimedeanFormula_eq_qwLambda_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (pkg : ConcreteCCM25ArithmeticPackage W f lambda) :
    ScopedRestrictedArchimedeanFormula W f lambda pkg =
      W.qwLambda lambda f f :=
  (qwLambda_eq_scopedRestrictedArchimedeanFormula_of_package pkg).symm

theorem source_global_finite_prime_evaluator_sum_eq_prime_power_filter
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let data := (formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData
    source_global_finite_prime_evaluator_sum h =
      ∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
        if hn : n ∈ W.globalPrimeIndexSet then
          PrimePowerArithmetic.MathlibFinitePrimeEvaluatorAtom W f f n (data.atIndex n hn)
        else
          0 := by
  dsimp [source_global_finite_prime_evaluator_sum]
  exact
    mathlib_global_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
      (formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData

theorem source_restricted_finite_prime_evaluator_sum_eq_prime_power_filter
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let data := (formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData
    source_restricted_finite_prime_evaluator_sum h =
      ∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
        if hn : n ∈ W.restrictedPrimeIndexSet lambda then
          PrimePowerArithmetic.MathlibFinitePrimeEvaluatorAtom W f f n (data.atIndex n hn)
        else
          0 := by
  dsimp [source_restricted_finite_prime_evaluator_sum]
  exact
    mathlib_restricted_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
      (formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData

theorem source_common_global_finite_prime_evaluator_sum_eq_prime_power_filter
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let data :=
      FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
        (formula_components h).commonCertificate
    source_common_global_finite_prime_evaluator_sum h =
      ∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
        if hn : n ∈ W.globalPrimeIndexSet then
          PrimePowerArithmetic.MathlibFinitePrimeEvaluatorAtom W f f n (data.atIndex n hn)
        else
          0 := by
  dsimp [source_common_global_finite_prime_evaluator_sum]
  exact
    mathlib_global_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
      (FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
        (formula_components h).commonCertificate)

theorem source_common_restricted_finite_prime_evaluator_sum_eq_prime_power_filter
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    let data :=
      FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
        (formula_components h).commonCertificate
    source_common_restricted_finite_prime_evaluator_sum h =
      ∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
        if hn : n ∈ W.restrictedPrimeIndexSet lambda then
          PrimePowerArithmetic.MathlibFinitePrimeEvaluatorAtom W f f n (data.atIndex n hn)
        else
          0 := by
  dsimp [source_common_restricted_finite_prime_evaluator_sum]
  exact
    mathlib_restricted_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
      (FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
        (formula_components h).commonCertificate)

theorem source_global_sum_eq_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_global_finite_prime_evaluator_sum h =
      source_common_global_finite_prime_evaluator_sum h := by
  dsimp [source_global_finite_prime_evaluator_sum,
    source_common_global_finite_prime_evaluator_sum]
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem source_restricted_sum_eq_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_restricted_finite_prime_evaluator_sum h =
      source_common_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_restricted_finite_prime_evaluator_sum,
    source_common_restricted_finite_prime_evaluator_sum]
  rw [(formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.restricted_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem source_global_source_evaluations_sum_eq_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_global_finite_prime_source_evaluations_sum h =
      source_common_global_finite_prime_source_evaluations_sum h := by
  dsimp [source_global_finite_prime_source_evaluations_sum,
    source_common_global_finite_prime_source_evaluations_sum]
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem source_restricted_source_evaluations_sum_eq_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_restricted_finite_prime_source_evaluations_sum h =
      source_common_restricted_finite_prime_source_evaluations_sum h := by
  dsimp [source_restricted_finite_prime_source_evaluations_sum,
    source_common_restricted_finite_prime_source_evaluations_sum]
  rw [(formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
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

theorem source_common_global_scoped_sum_eq_common_global_sum_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_common_global_finite_prime_evaluator_scoped_sum h =
      source_common_global_finite_prime_evaluator_sum h :=
  rfl

theorem source_common_restricted_scoped_sum_eq_common_restricted_sum_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    source_common_restricted_finite_prime_evaluator_scoped_sum h =
      source_common_restricted_finite_prime_evaluator_sum h :=
  rfl

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
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
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
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
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
  rw [(formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.restricted_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem psi_source_evaluations_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.psi (W.convolutionStar f f) =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          source_common_global_finite_prime_source_evaluations_sum h := by
  rw [FormulaComponents.psi_source_evaluations_of_formula_components
    (formula_components h)]
  dsimp [source_common_global_finite_prime_source_evaluations_sum]
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem qw_source_evaluations_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qw f f =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          source_common_global_finite_prime_source_evaluations_sum h := by
  rw [FormulaComponents.qw_source_evaluations_of_formula_components
    (formula_components h)]
  dsimp [source_common_global_finite_prime_source_evaluations_sum]
  rw [(formula_components h).global.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
  rw [FormulaComponents.global_certificate_eq_common_of_formula_components
    (formula_components h)]

theorem qw_lambda_formula_source_evaluations_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          source_common_restricted_finite_prime_source_evaluations_sum h := by
  rw [FormulaComponents.qw_lambda_formula_source_evaluations_of_formula_components
    (formula_components h)]
  dsimp [source_common_restricted_finite_prime_source_evaluations_sum]
  rw [(formula_components h).restricted.finitePrimeSumReadOff.scopedArithmeticData_eq_certificate]
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

theorem common_atom_source_evaluations_archimedean_contribution_matches_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (hbalance :
      W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_restricted_finite_prime_source_evaluations_sum h =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_global_finite_prime_source_evaluations_sum h) :
    W.archimedeanTerm (W.convolutionStar f f) +
        W.polePairing f -
          source_common_restricted_finite_prime_source_evaluations_sum h =
      W.poleFunctional (W.convolutionStar f f) -
        W.archimedeanTerm (W.convolutionStar f f) -
          source_common_global_finite_prime_source_evaluations_sum h := by
  rw [← source_restricted_source_evaluations_sum_eq_common_atoms_of_package h,
    ← source_global_source_evaluations_sum_eq_common_atoms_of_package h]
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

theorem qw_lambda_eq_qw_of_common_atom_scoped_archimedean_contribution
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (hbalance :
      W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_common_restricted_finite_prime_evaluator_scoped_sum h =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_common_global_finite_prime_evaluator_scoped_sum h) :
    W.qwLambda lambda f f = W.qw f f := by
  calc
    W.qwLambda lambda f f =
        W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_common_restricted_finite_prime_evaluator_scoped_sum h :=
      qw_lambda_formula_scoped_source_evaluator_common_atoms_of_package h
    _ =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_common_global_finite_prime_evaluator_scoped_sum h :=
      hbalance
    _ = W.qw f f :=
      (qw_scoped_source_evaluator_common_atoms_of_package h).symm

theorem qw_lambda_eq_qw_of_common_atom_source_evaluations_archimedean_contribution
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (hbalance :
      W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_common_restricted_finite_prime_source_evaluations_sum h =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_common_global_finite_prime_source_evaluations_sum h) :
    W.qwLambda lambda f f = W.qw f f := by
  calc
    W.qwLambda lambda f f =
        W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_common_restricted_finite_prime_source_evaluations_sum h :=
      qw_lambda_formula_source_evaluations_common_atoms_of_package h
    _ =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_common_global_finite_prime_source_evaluations_sum h :=
      hbalance
    _ = W.qw f f :=
      (qw_source_evaluations_common_atoms_of_package h).symm

theorem qw_lambda_eq_qw_of_source_evaluations_archimedean_contribution
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (hbalance :
      W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_restricted_finite_prime_source_evaluations_sum h =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_global_finite_prime_source_evaluations_sum h) :
    W.qwLambda lambda f f = W.qw f f :=
  qw_lambda_eq_qw_of_common_atom_source_evaluations_archimedean_contribution h
    (common_atom_source_evaluations_archimedean_contribution_matches_of_package h
      hbalance)

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

theorem qw_lambda_eq_qw_of_scoped_archimedean_contribution
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (hbalance :
      W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            source_restricted_finite_prime_evaluator_scoped_sum h =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) -
            source_global_finite_prime_evaluator_scoped_sum h) :
    W.qwLambda lambda f f = W.qw f f := by
  apply qw_lambda_eq_qw_of_common_atom_scoped_archimedean_contribution h
  rw [← source_restricted_scoped_sum_eq_common_scoped_atoms_of_package h,
    ← source_global_scoped_sum_eq_common_scoped_atoms_of_package h]
  exact hbalance

theorem global_finite_prime_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_global_finite_prime_evaluator_sum h := by
  dsimp [source_global_finite_prime_evaluator_sum]
  exact
    FormulaComponents.global_finite_prime_scoped_sum_of_formula_components
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
      source_global_finite_prime_evaluator_sum h := by
  dsimp [source_global_finite_prime_evaluator_sum]
  exact
    FormulaComponents.global_von_mangoldt_pairing_scoped_sum_of_formula_components
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
      source_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_restricted_finite_prime_evaluator_sum]
  exact
    FormulaComponents.restricted_finite_prime_scoped_sum_of_formula_components
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

theorem finite_prime_concrete_object_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    (n : ℕ) :
    let obj := finite_prime_concrete_object_of_package h
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        ((obj.atomData n).sourcePairing.model.sourceEvaluation.forwardValue +
          (obj.atomData n).sourcePairing.model.sourceEvaluation.inverseValue) :=
  FinitePrimeCertificate.concrete_object_pairing_formula_source_evaluations
    (finite_prime_concrete_object_of_package h) n

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
  by
    let sourceEvaluation :=
      ((finite_prime_concrete_object_of_package h).atomData n).sourcePairing.model.sourceEvaluation
    rw [finite_prime_concrete_object_pairing_formula_source_evaluations h n,
      PrimePowerEvaluation.source_forward_value_at_source_points sourceEvaluation,
      PrimePowerEvaluation.source_inverse_value_at_source_points sourceEvaluation]

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
    arithmetic_global_mathlib_sum_formula_of_certificate
      (formula_components h).commonCertificate

theorem finite_prime_concrete_object_restricted_sum_read_off
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_common_restricted_finite_prime_evaluator_sum]
  exact
    arithmetic_restricted_mathlib_sum_formula_of_certificate
      (formula_components h).commonCertificate

theorem finite_prime_concrete_object_global_pairing_sum_read_off
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_global_finite_prime_evaluator_sum h := by
  dsimp [source_common_global_finite_prime_evaluator_sum]
  exact
    arithmetic_global_mathlib_von_mangoldt_pairing_sum_formula_of_certificate
      (formula_components h).commonCertificate

theorem finite_prime_concrete_object_restricted_pairing_sum_read_off
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_common_restricted_finite_prime_evaluator_sum]
  exact
    arithmetic_restricted_mathlib_von_mangoldt_pairing_sum_formula_of_certificate
      (formula_components h).commonCertificate

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
        IsPrimePow n ∧
          W.finitePrimeAtomVisible n (W.convolutionStar f f) :=
  fun n => by
    exact (exact_support_of_package h).globalExact n

theorem restricted_exact_of_package_exact_support
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        IsPrimePow n ∧
          W.finitePrimeAtomVisible n (W.convolutionStar f f) ∧
            1 < n ∧ (n : ℝ) ≤ lambda ^ 2 :=
  fun n => by
    exact (exact_support_of_package h).restrictedExact n

theorem restricted_von_mangoldt_pairing_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_restricted_finite_prime_evaluator_sum h := by
  dsimp [source_restricted_finite_prime_evaluator_sum]
  exact
    FormulaComponents.restricted_von_mangoldt_pairing_scoped_sum_of_formula_components
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
    PrimePowerSupport.SourceGlobalIndexData W f f n := by
  have hdata :=
    (finite_prime_concrete_object_of_package h).globalIndexData hn
  exact
    { primePowerIndex :=
        FinitePrimeCertificate.concrete_object_global_index_prime_power
          (finite_prime_concrete_object_of_package h) hn
      atomVisible := hdata.atomVisible }

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
    PrimePowerSupport.SourceRestrictedIndexData W f f lambda n := by
  have hdata :=
    (finite_prime_concrete_object_of_package h).restrictedIndexData hn
  exact
    { primePowerIndex :=
        FinitePrimeCertificate.concrete_object_restricted_index_prime_power
          (finite_prime_concrete_object_of_package h) hn
      atomVisible := hdata.atomVisible
      lambdaCut := hdata.lambdaCut }

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
    PrimePowerSupport.SourceVisibleAtomData W f f n := by
  let hcert := (formula_components h).commonCertificate
  let hsource := (hcert.support.visibleIff n).1 hvisible
  exact
    { primePowerIndex := hsource.primePowerIndex
      atomVisible := hvisible }

theorem finite_prime_concrete_object_global_index_route_data
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerSupport.SourceGlobalIndexData W f f n where
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
    PrimePowerSupport.SourceRestrictedIndexData W f f lambda n where
  primePowerIndex :=
    (common_certificate_route_visible_atom_data_of_package h
      (finite_prime_concrete_object_restricted_index_route_visible h hn)).primePowerIndex
  atomVisible :=
    (common_certificate_route_visible_atom_data_of_package h
      (finite_prime_concrete_object_restricted_index_route_visible h hn)).atomVisible
  lambdaCut :=
    ((finite_prime_concrete_object_of_package h).restrictedIndexData hn).lambdaCut

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
    PrimePowerSupport.SourceGlobalIndexData W f f n := by
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
    PrimePowerSupport.SourceRestrictedIndexData W f f lambda n := by
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
    1 < n ∧ (n : ℝ) ≤ lambda ^ 2 :=
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
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  FinitePrimeCertificate.concrete_object_global_index_weight_read_off
    (finite_prime_concrete_object_of_package h) hn

theorem global_index_pairing_formula_source_evaluations_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom :=
      (finite_prime_concrete_object_of_package h).globalArithmeticData.atIndex
        n hn
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.forwardValue +
          atom.sourcePairing.model.sourceEvaluation.inverseValue) :=
  FinitePrimeCertificate.concrete_object_global_index_pairing_formula_source_evaluations
    (finite_prime_concrete_object_of_package h) hn

theorem global_index_pairing_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom :=
      (finite_prime_concrete_object_of_package h).globalArithmeticData.atIndex
        n hn
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f f) (n : ℝ) +
          atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f f) ((n : ℝ)⁻¹)) :=
  by
    let sourceEvaluation :=
      ((finite_prime_concrete_object_of_package h).globalArithmeticData.atIndex
        n hn).sourcePairing.model.sourceEvaluation
    rw [global_index_pairing_formula_source_evaluations_of_package h hn,
      PrimePowerEvaluation.source_forward_value_at_source_points sourceEvaluation,
      PrimePowerEvaluation.source_inverse_value_at_source_points sourceEvaluation]

theorem global_index_finite_prime_term_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f f :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_mathlib_pairing
    (finite_prime_concrete_object_of_package h).globalArithmeticData hn

theorem global_index_finite_prime_term_formula_source_evaluations_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom :=
      (finite_prime_concrete_object_of_package h).globalArithmeticData.atIndex
        n hn
    W.finitePrimeTerm n (W.convolutionStar f f) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  FinitePrimeCertificate.concrete_object_global_index_term_formula_source_evaluations
    (finite_prime_concrete_object_of_package h) hn

theorem global_index_von_mangoldt_pairing_formula_source_evaluations_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom :=
      (finite_prime_concrete_object_of_package h).globalArithmeticData.atIndex
        n hn
    W.vonMangoldtWeight n * W.primePowerPairing n f f =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  by
    exact
      concrete_object_global_index_von_mangoldt_pairing_formula_source_evaluations
        (finite_prime_concrete_object_of_package h) hn

theorem global_index_finite_prime_term_formula_scoped_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f f n
        ((finite_prime_concrete_object_of_package h).globalArithmeticData.atIndex
          n hn) :=
  FinitePrimeCertificate.concrete_object_global_index_term_formula_source_evaluator
    (finite_prime_concrete_object_of_package h) hn

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
    1 < n ∧ (n : ℝ) ≤ lambda ^ 2 :=
  common_certificate_restricted_index_lambda_cut_of_package h hn

theorem restricted_index_one_lt_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    1 < n :=
  (restricted_index_lambda_cut_of_package h hn).1

theorem restricted_index_le_lambda_sq_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  (restricted_index_lambda_cut_of_package h hn).2

theorem restricted_index_weight_read_off_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  FinitePrimeCertificate.concrete_object_restricted_index_weight_read_off
    (finite_prime_concrete_object_of_package h) hn

theorem restricted_index_pairing_formula_source_evaluations_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom :=
      (finite_prime_concrete_object_of_package h).restrictedArithmeticData.atIndex
        n hn
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.forwardValue +
          atom.sourcePairing.model.sourceEvaluation.inverseValue) :=
  FinitePrimeCertificate.concrete_object_restricted_index_pairing_formula_source_evaluations
    (finite_prime_concrete_object_of_package h) hn

theorem restricted_index_pairing_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom :=
      (finite_prime_concrete_object_of_package h).restrictedArithmeticData.atIndex
        n hn
    W.primePowerPairing n f f =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f f) (n : ℝ) +
          atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f f) ((n : ℝ)⁻¹)) :=
  by
    let sourceEvaluation :=
      ((finite_prime_concrete_object_of_package h).restrictedArithmeticData.atIndex
        n hn).sourcePairing.model.sourceEvaluation
    rw [restricted_index_pairing_formula_source_evaluations_of_package h hn,
      PrimePowerEvaluation.source_forward_value_at_source_points sourceEvaluation,
      PrimePowerEvaluation.source_inverse_value_at_source_points sourceEvaluation]

theorem restricted_index_finite_prime_term_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f f :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_mathlib_pairing
    (finite_prime_concrete_object_of_package h).restrictedArithmeticData hn

theorem restricted_index_finite_prime_term_formula_source_evaluations_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom :=
      (finite_prime_concrete_object_of_package h).restrictedArithmeticData.atIndex
        n hn
    W.finitePrimeTerm n (W.convolutionStar f f) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  FinitePrimeCertificate.concrete_object_restricted_index_term_formula_source_evaluations
    (finite_prime_concrete_object_of_package h) hn

theorem restricted_index_von_mangoldt_pairing_formula_source_evaluations_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom :=
      (finite_prime_concrete_object_of_package h).restrictedArithmeticData.atIndex
        n hn
    W.vonMangoldtWeight n * W.primePowerPairing n f f =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  by
    exact
      concrete_object_restricted_index_von_mangoldt_pairing_formula_source_evaluations
        (finite_prime_concrete_object_of_package h) hn

theorem restricted_index_finite_prime_term_formula_scoped_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f f n
        ((finite_prime_concrete_object_of_package h).restrictedArithmeticData.atIndex
          n hn) :=
  FinitePrimeCertificate.concrete_object_restricted_index_term_formula_source_evaluator
    (finite_prime_concrete_object_of_package h) hn

end Package
end CCM25Concrete
end Source
end ConnesWeilRH
