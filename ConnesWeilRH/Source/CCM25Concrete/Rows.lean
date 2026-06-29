/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface

/-!
# Concrete CCM25 arithmetic rows

This module contains the concrete CCM25 row data below the compact
`CCM25Interface` layer.  It deliberately does not import `ConnesWeilRH.Source.CCM25`;
the compact interface is assembled later, after these rows have been named.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace Rows

structure ConcreteGlobalQWPsiRows (W : WeilFormSymbols) where
  qwDefinition : WeilFormSymbols.QWDefinitionStatement W
  psiSign : WeilFormSymbols.PsiSignStatement W

structure ConcreteRestrictedQWLambdaRows (W : WeilFormSymbols) where
  qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W

structure ConcretePoleNormalizationRows (W : WeilFormSymbols) where
  poleNormalization : WeilFormSymbols.PoleNormalizationStatement W

structure ConcreteCCM25Rows (W : WeilFormSymbols) where
  globalRows : ConcreteGlobalQWPsiRows W
  restrictedRows : ConcreteRestrictedQWLambdaRows W
  finitePrimeCertificates :
    FinitePrimeInterface.FixedLambdaCertificatesForAllTests W
  poleRows : ConcretePoleNormalizationRows W

structure ConcreteCCM25AtomRows (W : WeilFormSymbols) where
  globalRows : ConcreteGlobalQWPsiRows W
  restrictedRows : ConcreteRestrictedQWLambdaRows W
  finitePrimeAtomCertificates :
    FinitePrimeInterface.FixedLambdaAtomCertificatesForAllTests W
  poleRows : ConcretePoleNormalizationRows W

structure ConcreteCCM25ArithmeticRows (W : WeilFormSymbols) where
  globalRows : ConcreteGlobalQWPsiRows W
  restrictedRows : ConcreteRestrictedQWLambdaRows W
  finitePrimeArithmeticCertificates :
    FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests W
  poleRows : ConcretePoleNormalizationRows W

def concrete_rows_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    ConcreteCCM25Rows W where
  globalRows := h.globalRows
  restrictedRows := h.restrictedRows
  finitePrimeCertificates :=
    FinitePrimeInterface.fixed_lambda_certificates_for_all_of_atom_certificates
      h.finitePrimeAtomCertificates
  poleRows := h.poleRows

noncomputable def atom_rows_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    ConcreteCCM25AtomRows W where
  globalRows := h.globalRows
  restrictedRows := h.restrictedRows
  finitePrimeAtomCertificates :=
    FinitePrimeInterface.fixed_lambda_atom_certificates_for_all_of_source_test_certificates
      h.finitePrimeArithmeticCertificates
  poleRows := h.poleRows

noncomputable def concrete_rows_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    ConcreteCCM25Rows W :=
  concrete_rows_of_atom_rows (atom_rows_of_arithmetic_rows h)

theorem finite_prime_normalization_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  FinitePrimeInterface.finite_prime_normalization_of_fixed_lambda_certificates
    h.finitePrimeCertificates

theorem finite_prime_normalization_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  FinitePrimeInterface.finite_prime_normalization_of_atom_certificates
    h.finitePrimeAtomCertificates

theorem finite_prime_normalization_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  FinitePrimeInterface.finite_prime_normalization_of_source_test_certificates
    h.finitePrimeArithmeticCertificates

def source_test_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) :
    PrimePowerTest.SourceTestEvaluationInterface W f g :=
  (h.finitePrimeArithmeticCertificates f g).sourceTest

theorem arithmetic_certificate_source_test_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    (((h.finitePrimeArithmeticCertificates f g).certificate
        lambda hlambda).support.sourceTest =
      source_test_of_arithmetic_rows h f g) :=
  (h.finitePrimeArithmeticCertificates f g).certificateSourceTest
    lambda hlambda

theorem arithmetic_atom_source_test_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    (n : ℕ) :
    ((((h.finitePrimeArithmeticCertificates f g).certificate
        lambda hlambda).atoms.atIndex n).sourceTest =
      source_test_of_arithmetic_rows h f g) :=
  FinitePrimeInterface.certificate_atom_source_test_of_source_test_certificates
    (h.finitePrimeArithmeticCertificates f g) lambda hlambda n

theorem arithmetic_atom_pairing_evaluation_source_test_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    (n : ℕ) :
    let atom :=
      ((h.finitePrimeArithmeticCertificates f g).certificate
        lambda hlambda).atoms.atIndex n
    atom.sourcePairing.model.sourceEvaluation.sourceTest =
      source_test_of_arithmetic_rows h f g :=
  FinitePrimeInterface.certificate_atom_pairing_evaluation_source_test_of_source_test_certificates
    (h.finitePrimeArithmeticCertificates f g) lambda hlambda n

theorem arithmetic_atom_visible_in_source_test_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    (n : ℕ) :
    (source_test_of_arithmetic_rows h f g).sourceAtomVisible n :=
  FinitePrimeInterface.certificate_atom_visible_in_source_test_of_source_test_certificates
    (h.finitePrimeArithmeticCertificates f g) lambda hlambda n

theorem arithmetic_atom_visible_in_pairing_source_test_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    (n : ℕ) :
    let atom :=
      ((h.finitePrimeArithmeticCertificates f g).certificate
        lambda hlambda).atoms.atIndex n
    atom.sourcePairing.model.sourceEvaluation.sourceTest.sourceAtomVisible n :=
  FinitePrimeInterface.certificate_atom_visible_in_pairing_source_test_of_source_test_certificates
    (h.finitePrimeArithmeticCertificates f g) lambda hlambda n

theorem finite_prime_visibility_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) :
    WeilFormSymbols.FinitePrimeVisibilityStatement W f g :=
  FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates
    (h.finitePrimeArithmeticCertificates f g)

noncomputable def fixed_lambda_concrete_object_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      W f g lambda :=
  FinitePrimeCertificate.concrete_object_of_arithmetic_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)

theorem fixed_lambda_concrete_object_certificate_eq
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    (fixed_lambda_concrete_object_of_arithmetic_rows h f g lambda hlambda).certificate =
      (h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda :=
  rfl

theorem arithmetic_global_sum_formula_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum W f g
        ((h.finitePrimeArithmeticCertificates f g).certificate
          lambda hlambda).atoms :=
  FinitePrimeCertificate.arithmetic_global_sum_formula_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)

theorem arithmetic_global_von_mangoldt_pairing_sum_formula_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum W f g
        ((h.finitePrimeArithmeticCertificates f g).certificate
          lambda hlambda).atoms :=
  FinitePrimeCertificate.arithmetic_global_von_mangoldt_pairing_sum_formula_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)

theorem arithmetic_restricted_sum_formula_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum W f g
        lambda
        ((h.finitePrimeArithmeticCertificates f g).certificate
          lambda hlambda).atoms :=
  FinitePrimeCertificate.arithmetic_restricted_sum_formula_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)

theorem arithmetic_restricted_von_mangoldt_pairing_sum_formula_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum W f g lambda
        ((h.finitePrimeArithmeticCertificates f g).certificate
          lambda hlambda).atoms :=
  FinitePrimeCertificate.arithmetic_restricted_von_mangoldt_pairing_sum_formula_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)

theorem arithmetic_global_index_prime_power_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  FinitePrimeCertificate.arithmetic_global_index_prime_power_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
    hn

theorem arithmetic_global_index_visible_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    (source_test_of_arithmetic_rows h f g).sourceAtomVisible n := by
  have hvisible :=
    FinitePrimeCertificate.arithmetic_global_index_visible_of_certificate
      ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
      hn
  simpa [arithmetic_certificate_source_test_of_arithmetic_rows
    h f g lambda hlambda] using hvisible

theorem arithmetic_global_index_source_data_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerArithmetic.SourcePrimePowerIndex n ∧
      (source_test_of_arithmetic_rows h f g).sourceAtomVisible n :=
  ⟨arithmetic_global_index_prime_power_of_arithmetic_rows
      h f g lambda hlambda hn,
    arithmetic_global_index_visible_of_arithmetic_rows
      h f g lambda hlambda hn⟩

theorem arithmetic_global_index_one_lt_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    1 < n :=
  PrimePowerArithmetic.source_prime_power_index_one_lt
    (arithmetic_global_index_prime_power_of_arithmetic_rows
      h f g lambda hlambda hn)

theorem arithmetic_restricted_index_prime_power_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  FinitePrimeCertificate.arithmetic_restricted_index_prime_power_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
    hn

theorem arithmetic_restricted_index_visible_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (source_test_of_arithmetic_rows h f g).sourceAtomVisible n := by
  have hvisible :=
    FinitePrimeCertificate.arithmetic_restricted_index_visible_of_certificate
      ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
      hn
  simpa [arithmetic_certificate_source_test_of_arithmetic_rows
    h f g lambda hlambda] using hvisible

theorem arithmetic_restricted_index_lambda_cut_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceLambdaCut lambda n :=
  FinitePrimeCertificate.arithmetic_restricted_index_lambda_cut_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
    hn

theorem arithmetic_restricted_index_source_data_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n ∧
      (source_test_of_arithmetic_rows h f g).sourceAtomVisible n ∧
        PrimePowerSupport.SourceLambdaCut lambda n :=
  ⟨arithmetic_restricted_index_prime_power_of_arithmetic_rows
      h f g lambda hlambda hn,
    arithmetic_restricted_index_visible_of_arithmetic_rows
      h f g lambda hlambda hn,
    arithmetic_restricted_index_lambda_cut_of_arithmetic_rows
      h f g lambda hlambda hn⟩

theorem arithmetic_restricted_index_one_lt_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    1 < n :=
  PrimePowerSupport.source_lambda_cut_one_lt
    (arithmetic_restricted_index_lambda_cut_of_arithmetic_rows
      h f g lambda hlambda hn)

theorem arithmetic_restricted_index_le_lambda_sq_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  FinitePrimeCertificate.arithmetic_restricted_index_le_lambda_sq_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
    hn

theorem arithmetic_source_weight_read_off_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    (n : ℕ) :
    W.vonMangoldtWeight n =
      PrimePowerArithmetic.SourceVonMangoldtWeight n :=
  PrimePowerArithmetic.source_weight_read_off
    (((h.finitePrimeArithmeticCertificates f g).certificate
      lambda hlambda).atoms.atIndex n)

theorem arithmetic_source_pairing_formula_source_evaluator_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    (n : ℕ) :
    let atom :=
      ((h.finitePrimeArithmeticCertificates f g).certificate
        lambda hlambda).atoms.atIndex n
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  PrimePowerArithmetic.source_pairing_formula_source_evaluator
    (((h.finitePrimeArithmeticCertificates f g).certificate
      lambda hlambda).atoms.atIndex n)

theorem arithmetic_finite_prime_term_formula_source_evaluator_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (((h.finitePrimeArithmeticCertificates f g).certificate
          lambda hlambda).atoms.atIndex n) :=
  PrimePowerArithmetic.source_finite_prime_term_formula_source_evaluator
    (((h.finitePrimeArithmeticCertificates f g).certificate
      lambda hlambda).atoms.atIndex n)

theorem qw_definition_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.QWDefinitionStatement W :=
  h.globalRows.qwDefinition

theorem psi_sign_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.PsiSignStatement W :=
  h.globalRows.psiSign

theorem qw_lambda_formula_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.QWLambdaFormulaStatement W :=
  h.restrictedRows.qwLambdaFormula

theorem pole_normalization_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.PoleNormalizationStatement W :=
  h.poleRows.poleNormalization

theorem qw_definition_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.QWDefinitionStatement W :=
  h.globalRows.qwDefinition

theorem psi_sign_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.PsiSignStatement W :=
  h.globalRows.psiSign

theorem qw_lambda_formula_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.QWLambdaFormulaStatement W :=
  h.restrictedRows.qwLambdaFormula

theorem pole_normalization_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.PoleNormalizationStatement W :=
  h.poleRows.poleNormalization

theorem qw_definition_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.QWDefinitionStatement W :=
  h.globalRows.qwDefinition

theorem psi_sign_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.PsiSignStatement W :=
  h.globalRows.psiSign

theorem qw_lambda_formula_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.QWLambdaFormulaStatement W :=
  h.restrictedRows.qwLambdaFormula

theorem pole_normalization_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.PoleNormalizationStatement W :=
  h.poleRows.poleNormalization

end Rows
end CCM25Concrete
end Source
end ConnesWeilRH
