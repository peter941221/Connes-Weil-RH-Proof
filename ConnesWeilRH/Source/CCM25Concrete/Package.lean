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

theorem global_finite_prime_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_global_finite_prime_evaluator_sum h := by
  rw [global_finite_prime_sum_of_package_components h,
    source_global_sum_eq_common_atoms_of_package h]

theorem global_von_mangoldt_pairing_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_global_finite_prime_evaluator_sum h :=
  FormulaComponents.global_von_mangoldt_pairing_sum_of_formula_components
    (formula_components h)

theorem global_von_mangoldt_pairing_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_global_finite_prime_evaluator_sum h := by
  rw [global_von_mangoldt_pairing_sum_of_package_components h,
    source_global_sum_eq_common_atoms_of_package h]

theorem restricted_finite_prime_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_restricted_finite_prime_evaluator_sum h :=
  FormulaComponents.restricted_finite_prime_sum_of_formula_components
    (formula_components h)

theorem restricted_finite_prime_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f f)) =
      source_common_restricted_finite_prime_evaluator_sum h := by
  rw [restricted_finite_prime_sum_of_package_components h,
    source_restricted_sum_eq_common_atoms_of_package h]

theorem restricted_index_set_eq_global_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    W.restrictedPrimeIndexSet lambda = W.globalPrimeIndexSet :=
  FinitePrimeCertificate.restricted_index_set_eq_global_of_arithmetic_certificate
    (formula_components h).commonCertificate

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

theorem restricted_von_mangoldt_pairing_sum_of_package_components
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_restricted_finite_prime_evaluator_sum h :=
  FormulaComponents.restricted_von_mangoldt_pairing_sum_of_formula_components
    (formula_components h)

theorem restricted_von_mangoldt_pairing_sum_common_atoms_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f) =
      source_common_restricted_finite_prime_evaluator_sum h := by
  rw [restricted_von_mangoldt_pairing_sum_of_package_components h,
    source_restricted_sum_eq_common_atoms_of_package h]

def source_test_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda) :
    PrimePowerTest.SourceTestEvaluationInterface W f f :=
  Interface.source_test_of_arithmetic_rows h.rows f f

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
    PrimePowerArithmetic.SourcePrimePowerIndex n ∧
      (source_test_of_package h).sourceAtomVisible n := by
  have hdata :=
    FinitePrimeCertificate.arithmetic_global_index_source_data_of_certificate
      (formula_components h).commonCertificate hn
  exact ⟨hdata.1, by
    rw [← common_certificate_source_test_of_package h]
    exact hdata.2⟩

theorem common_certificate_global_index_prime_power_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  (common_certificate_global_index_source_data_of_package h hn).1

theorem common_certificate_global_index_visible_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    (source_test_of_package h).sourceAtomVisible n :=
  (common_certificate_global_index_source_data_of_package h hn).2

theorem common_certificate_restricted_index_source_data_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n ∧
      (source_test_of_package h).sourceAtomVisible n ∧
        PrimePowerSupport.SourceLambdaCut lambda n := by
  have hdata :=
    FinitePrimeCertificate.arithmetic_restricted_index_source_data_of_certificate
      (formula_components h).commonCertificate hn
  exact ⟨hdata.1, by
    rw [← common_certificate_source_test_of_package h]
    exact hdata.2.1, hdata.2.2⟩

theorem common_certificate_restricted_index_prime_power_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  (common_certificate_restricted_index_source_data_of_package h hn).1

theorem common_certificate_restricted_index_visible_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (source_test_of_package h).sourceAtomVisible n :=
  (common_certificate_restricted_index_source_data_of_package h hn).2.1

theorem common_certificate_restricted_index_lambda_cut_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceLambdaCut lambda n :=
  (common_certificate_restricted_index_source_data_of_package h hn).2.2

theorem global_index_prime_power_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  common_certificate_global_index_prime_power_of_package h hn

theorem global_index_visible_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    (source_test_of_package h).sourceAtomVisible n :=
  common_certificate_global_index_visible_of_package h hn

theorem global_index_one_lt_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    1 < n :=
  PrimePowerArithmetic.source_prime_power_index_one_lt
    (global_index_prime_power_of_package h hn)

theorem global_index_weight_read_off_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.globalPrimeIndexSet) :
    W.vonMangoldtWeight n =
      PrimePowerArithmetic.SourceVonMangoldtWeight n :=
  PrimePowerArithmetic.source_weight_read_off
    ((formula_components h).commonCertificate.atoms.atIndex n)

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
  PrimePowerArithmetic.source_pairing_formula_source_evaluator
    ((formula_components h).commonCertificate.atoms.atIndex n)

theorem global_index_finite_prime_term_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f f n
        ((formula_components h).commonCertificate.atoms.atIndex n) :=
  PrimePowerArithmetic.source_finite_prime_term_formula_source_evaluator
    ((formula_components h).commonCertificate.atoms.atIndex n)

theorem restricted_index_prime_power_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  common_certificate_restricted_index_prime_power_of_package h hn

theorem restricted_index_visible_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (source_test_of_package h).sourceAtomVisible n :=
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
    W.vonMangoldtWeight n =
      PrimePowerArithmetic.SourceVonMangoldtWeight n :=
  PrimePowerArithmetic.source_weight_read_off
    ((formula_components h).commonCertificate.atoms.atIndex n)

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
  PrimePowerArithmetic.source_pairing_formula_source_evaluator
    ((formula_components h).commonCertificate.atoms.atIndex n)

theorem restricted_index_finite_prime_term_formula_source_evaluator_of_package
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : ConcreteCCM25ArithmeticPackage W f lambda)
    {n : ℕ} (_hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeTerm n (W.convolutionStar f f) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f f n
        ((formula_components h).commonCertificate.atoms.atIndex n) :=
  PrimePowerArithmetic.source_finite_prime_term_formula_source_evaluator
    ((formula_components h).commonCertificate.atoms.atIndex n)

end Package
end CCM25Concrete
end Source
end ConnesWeilRH
