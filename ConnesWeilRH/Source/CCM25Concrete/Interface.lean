/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.Global
import ConnesWeilRH.Source.CCM25Concrete.Restricted
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface

/-!
# Constructing the CCM25 source interface from concrete rows

This module is a constructor layer for `CCM25Interface`.  It does not prove the
analytic CCM25 rows; it states the exact concrete rows that are sufficient to
build the interface consumed by the route.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace Interface

structure ConcreteCCM25Rows (W : WeilFormSymbols) where
  qwDefinition : WeilFormSymbols.QWDefinitionStatement W
  psiSign : WeilFormSymbols.PsiSignStatement W
  qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W
  finitePrimeCertificates :
    FinitePrimeInterface.FixedLambdaCertificatesForAllTests W
  poleNormalization : WeilFormSymbols.PoleNormalizationStatement W

structure ConcreteCCM25AtomRows (W : WeilFormSymbols) where
  qwDefinition : WeilFormSymbols.QWDefinitionStatement W
  psiSign : WeilFormSymbols.PsiSignStatement W
  qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W
  finitePrimeAtomCertificates :
    FinitePrimeInterface.FixedLambdaAtomCertificatesForAllTests W
  poleNormalization : WeilFormSymbols.PoleNormalizationStatement W

structure ConcreteCCM25ArithmeticRows (W : WeilFormSymbols) where
  qwDefinition : WeilFormSymbols.QWDefinitionStatement W
  psiSign : WeilFormSymbols.PsiSignStatement W
  qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W
  finitePrimeArithmeticCertificates :
    FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests W
  poleNormalization : WeilFormSymbols.PoleNormalizationStatement W

def ccm25_interface_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    CCM25Interface where
  weilSymbols := W
  qwDefinition := ⟨h.qwDefinition, h.psiSign⟩
  qwLambdaFormula := h.qwLambdaFormula
  finitePrimeNormalization :=
    FinitePrimeInterface.finite_prime_normalization_of_fixed_lambda_certificates
      h.finitePrimeCertificates
  poleNormalization := h.poleNormalization

def concrete_rows_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    ConcreteCCM25Rows W where
  qwDefinition := h.qwDefinition
  psiSign := h.psiSign
  qwLambdaFormula := h.qwLambdaFormula
  finitePrimeCertificates :=
    FinitePrimeInterface.fixed_lambda_certificates_for_all_of_atom_certificates
      h.finitePrimeAtomCertificates
  poleNormalization := h.poleNormalization

def atom_rows_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    ConcreteCCM25AtomRows W where
  qwDefinition := h.qwDefinition
  psiSign := h.psiSign
  qwLambdaFormula := h.qwLambdaFormula
  finitePrimeAtomCertificates :=
    FinitePrimeInterface.fixed_lambda_atom_certificates_for_all_of_source_test_certificates
      h.finitePrimeArithmeticCertificates
  poleNormalization := h.poleNormalization

def concrete_rows_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    ConcreteCCM25Rows W :=
  concrete_rows_of_atom_rows (atom_rows_of_arithmetic_rows h)

def ccm25_interface_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    CCM25Interface :=
  ccm25_interface_of_concrete_rows (concrete_rows_of_atom_rows h)

def ccm25_interface_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    CCM25Interface :=
  ccm25_interface_of_atom_rows (atom_rows_of_arithmetic_rows h)

theorem finite_prime_normalization_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  (ccm25_interface_of_concrete_rows h).finitePrimeNormalization

theorem finite_prime_normalization_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  (ccm25_interface_of_atom_rows h).finitePrimeNormalization

theorem finite_prime_normalization_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  (ccm25_interface_of_arithmetic_rows h).finitePrimeNormalization

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

theorem arithmetic_global_index_one_lt_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    1 < n :=
  FinitePrimeCertificate.arithmetic_global_index_one_lt_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
    hn

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

theorem arithmetic_restricted_index_one_lt_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    1 < n :=
  FinitePrimeCertificate.arithmetic_restricted_index_one_lt_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
    hn

theorem arithmetic_restricted_index_le_lambda_sq_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  FinitePrimeCertificate.arithmetic_restricted_index_le_lambda_sq_of_certificate
    ((h.finitePrimeArithmeticCertificates f g).certificate lambda hlambda)
    hn

theorem qw_definition_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.QWDefinitionStatement W :=
  (ccm25_interface_of_concrete_rows h).qwDefinition.1

theorem psi_sign_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.PsiSignStatement W :=
  (ccm25_interface_of_concrete_rows h).qwDefinition.2

theorem qw_lambda_formula_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.QWLambdaFormulaStatement W :=
  (ccm25_interface_of_concrete_rows h).qwLambdaFormula

theorem pole_normalization_of_concrete_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25Rows W) :
    WeilFormSymbols.PoleNormalizationStatement W :=
  (ccm25_interface_of_concrete_rows h).poleNormalization

theorem qw_definition_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.QWDefinitionStatement W :=
  (ccm25_interface_of_atom_rows h).qwDefinition.1

theorem psi_sign_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.PsiSignStatement W :=
  (ccm25_interface_of_atom_rows h).qwDefinition.2

theorem qw_lambda_formula_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.QWLambdaFormulaStatement W :=
  (ccm25_interface_of_atom_rows h).qwLambdaFormula

theorem pole_normalization_of_atom_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25AtomRows W) :
    WeilFormSymbols.PoleNormalizationStatement W :=
  (ccm25_interface_of_atom_rows h).poleNormalization

theorem qw_definition_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.QWDefinitionStatement W :=
  (ccm25_interface_of_arithmetic_rows h).qwDefinition.1

theorem psi_sign_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.PsiSignStatement W :=
  (ccm25_interface_of_arithmetic_rows h).qwDefinition.2

theorem qw_lambda_formula_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.QWLambdaFormulaStatement W :=
  (ccm25_interface_of_arithmetic_rows h).qwLambdaFormula

theorem pole_normalization_of_arithmetic_rows
    {W : WeilFormSymbols} (h : ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.PoleNormalizationStatement W :=
  (ccm25_interface_of_arithmetic_rows h).poleNormalization

end Interface
end CCM25Concrete
end Source
end ConnesWeilRH
