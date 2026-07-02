/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate

/-!
# CCM25 finite-prime interface from fixed-lambda certificates

This module is the bridge from concrete fixed-lambda prime-power certificates to
the broad CCM25 finite-prime normalization interface.  It keeps the quantifier
shift explicit: the broad interface follows only from a certificate for every
`lambda` with `1 < lambda`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FinitePrimeInterface

def FixedLambdaCertificatesForTest
    (W : WeilFormSymbols) (f g : TestFunction) : Type 1 :=
  ∀ lambda : ℝ,
    1 < lambda →
      FinitePrimeCertificate.FixedLambdaFinitePrimeCertificate W f g lambda

def FixedLambdaCertificatesForAllTests
    (W : WeilFormSymbols) : Type 1 :=
  ∀ f g : TestFunction, FixedLambdaCertificatesForTest W f g

def FixedLambdaAtomCertificatesForTest
    (W : WeilFormSymbols) (f g : TestFunction) : Type 1 :=
  ∀ lambda : ℝ,
    1 < lambda →
      FinitePrimeCertificate.FixedLambdaFinitePrimeAtomCertificate
        W f g lambda

def FixedLambdaAtomCertificatesForAllTests
    (W : WeilFormSymbols) : Type 1 :=
  ∀ f g : TestFunction, FixedLambdaAtomCertificatesForTest W f g

def FixedLambdaArithmeticCertificatesForTest
    (W : WeilFormSymbols) (f g : TestFunction) : Type 1 :=
  ∀ lambda : ℝ,
    1 < lambda →
      FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
        W f g lambda

def FixedLambdaArithmeticCertificatesForAllTests
    (W : WeilFormSymbols) : Type 1 :=
  ∀ f g : TestFunction, FixedLambdaArithmeticCertificatesForTest W f g

structure FixedLambdaArithmeticSourceTestCertificatesForTest
    (W : WeilFormSymbols) (f g : TestFunction) where
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g
  certificate :
    ∀ lambda : ℝ,
      1 < lambda →
        FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
          W f g lambda
  certificateSourceTest :
    ∀ (lambda : ℝ) (hlambda : 1 < lambda),
      (certificate lambda hlambda).support.sourceTest = sourceTest

def FixedLambdaArithmeticSourceTestCertificatesForAllTests
    (W : WeilFormSymbols) : Type 1 :=
  ∀ f g : TestFunction,
    FixedLambdaArithmeticSourceTestCertificatesForTest W f g

def fixed_lambda_certificates_of_atom_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaAtomCertificatesForTest W f g) :
    FixedLambdaCertificatesForTest W f g := by
  intro lambda hlambda
  exact FinitePrimeCertificate.certificate_of_atom_certificate
    (h lambda hlambda)

def fixed_lambda_certificates_for_all_of_atom_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaAtomCertificatesForAllTests W) :
    FixedLambdaCertificatesForAllTests W := by
  intro f g
  exact fixed_lambda_certificates_of_atom_certificates (h f g)

noncomputable def fixed_lambda_atom_certificates_of_arithmetic_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticCertificatesForTest W f g) :
    FixedLambdaAtomCertificatesForTest W f g := by
  intro lambda hlambda
  exact FinitePrimeCertificate.atom_certificate_of_arithmetic_certificate
    (h lambda hlambda)

noncomputable def fixed_lambda_atom_certificates_for_all_of_arithmetic_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaArithmeticCertificatesForAllTests W) :
    FixedLambdaAtomCertificatesForAllTests W := by
  intro f g
  exact fixed_lambda_atom_certificates_of_arithmetic_certificates (h f g)

noncomputable def fixed_lambda_certificates_of_arithmetic_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticCertificatesForTest W f g) :
    FixedLambdaCertificatesForTest W f g :=
  fixed_lambda_certificates_of_atom_certificates
    (fixed_lambda_atom_certificates_of_arithmetic_certificates h)

noncomputable def fixed_lambda_certificates_for_all_of_arithmetic_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaArithmeticCertificatesForAllTests W) :
    FixedLambdaCertificatesForAllTests W :=
  fixed_lambda_certificates_for_all_of_atom_certificates
    (fixed_lambda_atom_certificates_for_all_of_arithmetic_certificates h)

def fixed_lambda_arithmetic_certificates_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g) :
    FixedLambdaArithmeticCertificatesForTest W f g := by
  intro lambda hlambda
  exact h.certificate lambda hlambda

def fixed_lambda_arithmetic_certificates_for_all_of_source_test_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaArithmeticSourceTestCertificatesForAllTests W) :
    FixedLambdaArithmeticCertificatesForAllTests W := by
  intro f g
  exact fixed_lambda_arithmetic_certificates_of_source_test_certificates
    (h f g)

noncomputable def fixed_lambda_atom_certificates_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g) :
    FixedLambdaAtomCertificatesForTest W f g :=
  fixed_lambda_atom_certificates_of_arithmetic_certificates
    (fixed_lambda_arithmetic_certificates_of_source_test_certificates h)

noncomputable def fixed_lambda_atom_certificates_for_all_of_source_test_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaArithmeticSourceTestCertificatesForAllTests W) :
    FixedLambdaAtomCertificatesForAllTests W :=
  fixed_lambda_atom_certificates_for_all_of_arithmetic_certificates
    (fixed_lambda_arithmetic_certificates_for_all_of_source_test_certificates h)

noncomputable def fixed_lambda_certificates_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g) :
    FixedLambdaCertificatesForTest W f g :=
  fixed_lambda_certificates_of_arithmetic_certificates
    (fixed_lambda_arithmetic_certificates_of_source_test_certificates h)

noncomputable def fixed_lambda_certificates_for_all_of_source_test_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaArithmeticSourceTestCertificatesForAllTests W) :
    FixedLambdaCertificatesForAllTests W :=
  fixed_lambda_certificates_for_all_of_arithmetic_certificates
    (fixed_lambda_arithmetic_certificates_for_all_of_source_test_certificates h)

def source_test_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g) :
    PrimePowerTest.SourceTestEvaluationInterface W f g :=
  h.sourceTest

theorem certificate_source_test_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (h.certificate lambda hlambda).support.sourceTest = h.sourceTest :=
  h.certificateSourceTest lambda hlambda

theorem certificate_atom_source_test_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g)
    (lambda : ℝ) (hlambda : 1 < lambda) (n : ℕ) :
    ((h.certificate lambda hlambda).atoms.atIndex n).sourceTest =
      h.sourceTest := by
  rw [FinitePrimeCertificate.arithmetic_atom_source_test_of_certificate,
    h.certificateSourceTest lambda hlambda]

theorem certificate_atom_pairing_evaluation_source_test_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g)
    (lambda : ℝ) (hlambda : 1 < lambda) (n : ℕ) :
    let atom := (h.certificate lambda hlambda).atoms.atIndex n
    atom.sourcePairing.model.sourceEvaluation.sourceTest = h.sourceTest := by
  dsimp
  rw [
    FinitePrimeCertificate.arithmetic_atom_pairing_evaluation_source_test_of_certificate,
    h.certificateSourceTest lambda hlambda]

theorem certificate_atom_visible_in_source_test_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g)
    (lambda : ℝ) (hlambda : 1 < lambda) (n : ℕ) :
    h.sourceTest.sourceAtomVisible n := by
  have hvisible :=
    FinitePrimeCertificate.arithmetic_atom_visible_in_support_source_test_of_certificate
      (h.certificate lambda hlambda) n
  simpa [h.certificateSourceTest lambda hlambda] using hvisible

theorem certificate_atom_visible_in_pairing_source_test_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g)
    (lambda : ℝ) (hlambda : 1 < lambda) (n : ℕ) :
    let atom := (h.certificate lambda hlambda).atoms.atIndex n
    atom.sourcePairing.model.sourceEvaluation.sourceTest.sourceAtomVisible n :=
  FinitePrimeCertificate.arithmetic_atom_visible_in_pairing_source_test_of_certificate
    (h.certificate lambda hlambda) n

theorem finite_prime_visibility_of_fixed_lambda_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaCertificatesForTest W f g) :
    WeilFormSymbols.FinitePrimeVisibilityStatement W f g := by
  let hcert := h 2 (by norm_num : (1 : ℝ) < 2)
  refine
    { globalPrimeIndexCoverage := ?_
      restrictedPrimeIndexCoverage := ?_
      finitePrimeTermNormalization := ?_ }
  · intro n hn
    let hvisible :=
      (FinitePrimeCertificate.visible_iff_of_certificate hcert n).1 hn
    exact FinitePrimeCertificate.global_exact_of_certificate
      hcert n |>.2
      { primePowerIndex := hvisible.primePowerIndex
        atomVisible := hvisible.atomVisible }
  · intro lambda hlambda
    let hcertLambda := h lambda hlambda
    exact (FinitePrimeCertificate.visibility_at_lambda_of_certificate
      hcertLambda).2.1
  · exact FinitePrimeCertificate.term_normalization_of_certificate
      hcert

theorem finite_prime_normalization_of_fixed_lambda_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaCertificatesForAllTests W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W := by
  intro f g
  exact finite_prime_visibility_of_fixed_lambda_certificates (h f g)

theorem finite_prime_visibility_of_atom_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaAtomCertificatesForTest W f g) :
    WeilFormSymbols.FinitePrimeVisibilityStatement W f g :=
  finite_prime_visibility_of_fixed_lambda_certificates
    (fixed_lambda_certificates_of_atom_certificates h)

theorem finite_prime_normalization_of_atom_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaAtomCertificatesForAllTests W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  finite_prime_normalization_of_fixed_lambda_certificates
    (fixed_lambda_certificates_for_all_of_atom_certificates h)

theorem finite_prime_visibility_of_arithmetic_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticCertificatesForTest W f g) :
    WeilFormSymbols.FinitePrimeVisibilityStatement W f g :=
  finite_prime_visibility_of_atom_certificates
    (fixed_lambda_atom_certificates_of_arithmetic_certificates h)

theorem finite_prime_normalization_of_arithmetic_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaArithmeticCertificatesForAllTests W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  finite_prime_normalization_of_atom_certificates
    (fixed_lambda_atom_certificates_for_all_of_arithmetic_certificates h)

theorem finite_prime_visibility_of_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g) :
    WeilFormSymbols.FinitePrimeVisibilityStatement W f g :=
  finite_prime_visibility_of_arithmetic_certificates
    (fixed_lambda_arithmetic_certificates_of_source_test_certificates h)

theorem finite_prime_normalization_of_source_test_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaArithmeticSourceTestCertificatesForAllTests W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  finite_prime_normalization_of_arithmetic_certificates
    (fixed_lambda_arithmetic_certificates_for_all_of_source_test_certificates h)

theorem finite_prime_visibility_of_common_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g) :
    WeilFormSymbols.FinitePrimeVisibilityStatement W f g := by
  let hbase := h.certificate 2 (by norm_num : (1 : ℝ) < 2)
  refine
    { globalPrimeIndexCoverage := ?_
      restrictedPrimeIndexCoverage := ?_
      finitePrimeTermNormalization := ?_ }
  · intro n hn
    let hvisible :=
      (FinitePrimeCertificate.visible_iff_of_certificate
        (FinitePrimeCertificate.certificate_of_arithmetic_certificate hbase)
        n).1 hn
    exact FinitePrimeCertificate.global_exact_of_certificate
      (FinitePrimeCertificate.certificate_of_arithmetic_certificate hbase) n |>.2
      { primePowerIndex := hvisible.primePowerIndex
        atomVisible := hvisible.atomVisible }
  · intro lambda hlambda
    let hcert := h.certificate lambda hlambda
    exact (FinitePrimeCertificate.visibility_at_lambda_of_certificate
      (FinitePrimeCertificate.certificate_of_arithmetic_certificate hcert)).2.1
  · exact FinitePrimeCertificate.arithmetic_term_normalization_of_certificate
      hbase

theorem finite_prime_term_normalization_of_common_source_test_certificates
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : FixedLambdaArithmeticSourceTestCertificatesForTest W f g) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g := by
  let hbase := h.certificate 2 (by norm_num : (1 : ℝ) < 2)
  exact FinitePrimeCertificate.arithmetic_term_normalization_of_certificate
    hbase

theorem finite_prime_normalization_of_common_source_test_certificates
    {W : WeilFormSymbols}
    (h : FixedLambdaArithmeticSourceTestCertificatesForAllTests W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W := by
  intro f g
  exact finite_prime_visibility_of_common_source_test_certificates (h f g)

end FinitePrimeInterface
end CCM25Concrete
end Source
end ConnesWeilRH
