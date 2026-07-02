/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.Objects
import ConnesWeilRH.Source.ObjectTheoremBasePackage
import ConnesWeilRH.Source.CC20Concrete.TraceScale

/-!
# Source-object expanded row staging

Goal 2C groups the expanded row data needed by `SourceObjectPackage` without
constructing a full source-object package.  The CCM25 row is derived from the
same concrete arithmetic rows used by Goal 0E, while CCM24 and CC20 remain
explicit expanded-row inputs.
-/

namespace ConnesWeilRH
namespace Source

/--
Common source-test data for Goal 2C.

The record forces the CCM25 arithmetic rows to use the same source evaluator as
the common source test.  This is the equality that later fills the
`SourceObjectPackage.ccm25Test_eq_commonTest` field.
-/
structure SourceObjectCommonData
    (base : SourceObjectTheoremBasePackage) where
  commonTest :
    SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows :
    CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      base.ccm25Model.toWeilFormSymbols
  ccm25Test_eq_commonTest :
    commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        concreteArithmeticRows commonTest.sourceTest commonTest.sourceTest
  finitePrimeNormalization :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      base.ccm25Model.toWeilFormSymbols

/--
Concrete common-test data for Goal 2C.

This is the narrow Block 1 seed below `SourceObjectCommonData`: it fixes the
common source test first, then requires the CCM25 arithmetic rows to expose the
same source-test interface at the pair `(g,g)`.  It avoids constructing a full
`SourceObjectPackage`, whose CCM24/CC20/RH-exit fields remain separate
analytic obligations.
-/
structure SourceObjectConcreteCommonData
    (base : SourceObjectTheoremBasePackage) where
  concreteCommonTest :
    CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
      base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows :
    CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      base.ccm25Model.toWeilFormSymbols
  arithmeticRowsUseConcreteCommonTest :
    CCM25Concrete.Rows.source_test_of_arithmetic_rows
        concreteArithmeticRows concreteCommonTest.sourceTest
        concreteCommonTest.sourceTest =
      concreteCommonTest.toSourceTestEvaluationInterface
  scopedArchimedeanContributionBalance :
    ∀ lambda : ℝ,
      ∀ pkg : CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        base.ccm25Model.toWeilFormSymbols concreteCommonTest.sourceTest
        lambda,
        CCM25Concrete.FinitePrimeSourceData.ScopedArchimedeanContributionBalance
          base.ccm25Model.toWeilFormSymbols concreteCommonTest.sourceTest
          lambda pkg

namespace SourceObjectConcreteCommonData

open CCM25Concrete

def ofSameSourceTest
    {base : SourceObjectTheoremBasePackage}
    (common :
      CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
        base.ccm25Model.toWeilFormSymbols)
    (rows :
      CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        base.ccm25Model.toWeilFormSymbols)
    (sameSourceTest :
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
          rows common.sourceTest common.sourceTest =
        common.toSourceTestEvaluationInterface)
    (scopedArchimedeanContributionBalance :
      ∀ lambda : ℝ,
        ∀ pkg : CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
          base.ccm25Model.toWeilFormSymbols common.sourceTest lambda,
          CCM25Concrete.FinitePrimeSourceData.ScopedArchimedeanContributionBalance
            base.ccm25Model.toWeilFormSymbols common.sourceTest lambda pkg) :
    SourceObjectConcreteCommonData base where
  concreteCommonTest := common
  concreteArithmeticRows := rows
  arithmeticRowsUseConcreteCommonTest := sameSourceTest
  scopedArchimedeanContributionBalance :=
    scopedArchimedeanContributionBalance

def ofCommonPairSourceTest
    {base : SourceObjectTheoremBasePackage}
    (common :
      CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
        base.ccm25Model.toWeilFormSymbols)
    (rows :
      CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        base.ccm25Model.toWeilFormSymbols)
    (commonPairSourceTest :
      (rows.finitePrimeArithmeticCertificates
          common.sourceTest common.sourceTest).sourceTest =
        common.toSourceTestEvaluationInterface)
    (scopedArchimedeanContributionBalance :
      ∀ lambda : ℝ,
        ∀ pkg : CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
          base.ccm25Model.toWeilFormSymbols common.sourceTest lambda,
          CCM25Concrete.FinitePrimeSourceData.ScopedArchimedeanContributionBalance
            base.ccm25Model.toWeilFormSymbols common.sourceTest lambda pkg) :
    SourceObjectConcreteCommonData base :=
  ofSameSourceTest common rows (by
    simpa [CCM25Concrete.Rows.source_test_of_arithmetic_rows]
      using commonPairSourceTest)
    scopedArchimedeanContributionBalance

def commonTest
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols :=
  SourceObject.CommonTestObject.ofConcrete data.concreteCommonTest

def toSourceObjectCommonData
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    SourceObjectCommonData base where
  commonTest := data.commonTest
  concreteArithmeticRows := data.concreteArithmeticRows
  ccm25Test_eq_commonTest := data.arithmeticRowsUseConcreteCommonTest.symm
  finitePrimeNormalization :=
    CCM25Concrete.FinitePrimeInterface.finite_prime_normalization_of_source_test_certificates
      (CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
        (CCM25Concrete.FinitePrimeSourceData.commonFinitePrimeArithmeticSourceDataOfArithmeticRows
          data.concreteCommonTest.sourceTest
          data.concreteArithmeticRows
          data.arithmeticRowsUseConcreteCommonTest
          data.scopedArchimedeanContributionBalance))

theorem common_test_eq_of_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest =
      SourceObject.CommonTestObject.ofConcrete data.concreteCommonTest :=
  rfl

theorem source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest.sourceTest =
      data.concreteCommonTest.sourceTest :=
  rfl

theorem source_convolution_square_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest.sourceConvolutionSquare =
      data.concreteCommonTest.sourceConvolutionSquare :=
  rfl

theorem ccm25_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest.ccm25SourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface :=
  rfl

theorem arithmetic_rows_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    CCM25Concrete.Rows.source_test_of_arithmetic_rows
        data.concreteArithmeticRows data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface :=
  data.arithmeticRowsUseConcreteCommonTest

theorem common_certificate_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    ((data.concreteArithmeticRows.finitePrimeArithmeticCertificates
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest).certificate
        lambda hlambda).support.sourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface := by
  calc
    (((data.concreteArithmeticRows.finitePrimeArithmeticCertificates
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest).certificate
        lambda hlambda).support.sourceTest)
        =
      (data.concreteArithmeticRows.finitePrimeArithmeticCertificates
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest).sourceTest :=
        (data.concreteArithmeticRows.finitePrimeArithmeticCertificates
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest).certificateSourceTest lambda hlambda
    _ = data.concreteCommonTest.toSourceTestEvaluationInterface :=
        by
          simpa [CCM25Concrete.Rows.source_test_of_arithmetic_rows]
            using data.arithmeticRowsUseConcreteCommonTest

theorem common_atom_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) (n : ℕ) :
    (((data.concreteArithmeticRows.finitePrimeArithmeticCertificates
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest).certificate
        lambda hlambda).atoms.atIndex n).sourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface := by
  let hcert :=
    (data.concreteArithmeticRows.finitePrimeArithmeticCertificates
      data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest).certificate lambda hlambda
  calc
    (hcert.atoms.atIndex n).sourceTest = hcert.support.sourceTest :=
        hcert.atomsUseSupportSourceTest n
    _ = data.concreteCommonTest.toSourceTestEvaluationInterface :=
        by
          simpa [hcert]
            using data.common_certificate_source_test_eq_concrete lambda hlambda

theorem common_atom_pairing_evaluation_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) (n : ℕ) :
    let atom :=
      ((data.concreteArithmeticRows.finitePrimeArithmeticCertificates
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest).certificate
        lambda hlambda).atoms.atIndex n
    atom.sourcePairing.model.sourceEvaluation.sourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface := by
  dsimp
  let hcert :=
    (data.concreteArithmeticRows.finitePrimeArithmeticCertificates
      data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest).certificate lambda hlambda
  calc
    (hcert.atoms.atIndex n).sourcePairing.model.sourceEvaluation.sourceTest =
      hcert.support.sourceTest :=
        PrimePowerArithmetic.source_pairing_evaluation_uses_normalization_source_test
          hcert.atomsUseSupportSourceTest n
    _ = data.concreteCommonTest.toSourceTestEvaluationInterface :=
        by
          simpa [hcert]
            using data.common_certificate_source_test_eq_concrete lambda hlambda

theorem common_atom_visible_in_concrete_source_test
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) (n : ℕ) :
    data.concreteCommonTest.sourceAtomVisible n := by
  let hcert :=
    (data.concreteArithmeticRows.finitePrimeArithmeticCertificates
      data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest).certificate lambda hlambda
  have hvisible :
      hcert.support.sourceTest.sourceAtomVisible n :=
    PrimePowerArithmetic.source_atom_visible_uses_normalization_source_test
      hcert.atomsUseSupportSourceTest n
  simpa [hcert, data.common_certificate_source_test_eq_concrete lambda hlambda]
    using hvisible

def commonArithmeticCertificate
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda :=
  (data.concreteArithmeticRows.finitePrimeArithmeticCertificates
    data.concreteCommonTest.sourceTest
    data.concreteCommonTest.sourceTest).certificate lambda hlambda

noncomputable def commonArithmeticPackage
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      lambda where
  rows := data.concreteArithmeticRows
  oneLtLambda := hlambda

noncomputable def commonFinitePrimeConcreteObject
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda :=
  CCM25Concrete.FinitePrimeCertificate.concrete_object_of_arithmetic_certificate
    (data.commonArithmeticCertificate lambda hlambda)

theorem common_finite_prime_concrete_object_certificate_eq
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (data.commonFinitePrimeConcreteObject lambda hlambda).certificate =
      data.commonArithmeticCertificate lambda hlambda :=
  rfl

theorem common_finite_prime_concrete_object_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (data.commonFinitePrimeConcreteObject lambda hlambda).sourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface := by
  calc
    (data.commonFinitePrimeConcreteObject lambda hlambda).sourceTest =
        (data.commonArithmeticCertificate lambda hlambda).support.sourceTest :=
      rfl
    _ = data.concreteCommonTest.toSourceTestEvaluationInterface :=
      data.common_certificate_source_test_eq_concrete lambda hlambda

theorem common_finite_prime_concrete_object_global_visible
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet) :
    base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
      (base.ccm25Model.toWeilFormSymbols.convolutionStar
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest) := by
  have hvisible :
      (data.commonFinitePrimeConcreteObject
        lambda hlambda).sourceTest.sourceAtomVisible n :=
    CCM25Concrete.FinitePrimeCertificate.concrete_object_global_index_visible
      (data.commonFinitePrimeConcreteObject lambda hlambda) hn
  have hcommon : data.concreteCommonTest.sourceAtomVisible n := by
    simpa [data.common_finite_prime_concrete_object_source_test_eq_concrete
      lambda hlambda] using hvisible
  exact (data.concreteCommonTest.route_visibility_iff_source_visibility n).2 hcommon

theorem common_route_visible_atom_data
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hvisible :
      base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) :
    CCM25Concrete.PrimePowerSupport.SourceVisibleAtomData
      IsPrimePow
      (fun n =>
        base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest)) n := by
  let hcert := data.commonArithmeticCertificate lambda hlambda
  let hsource :=
    (CCM25Concrete.FinitePrimeCertificate.visible_iff_of_certificate
      (CCM25Concrete.FinitePrimeCertificate.certificate_of_arithmetic_certificate
        hcert) n).1 hvisible
  have hroute :
      base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) := hvisible
  have hprime : CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex n := by
    simpa [
      CCM25Concrete.FinitePrimeCertificate.certificate_of_arithmetic_certificate,
      CCM25Concrete.FinitePrimeCertificate.atom_certificate_of_arithmetic_certificate,
      CCM25Concrete.PrimePowerSupport.support_skeleton_of_arithmetic_support_skeleton]
      using hsource.primePowerIndex
  exact
    { primePowerIndex :=
        CCM25Concrete.PrimePowerArithmetic.source_prime_power_index_iff_mathlib.1
          hprime
      atomVisible := hroute }

theorem common_finite_prime_concrete_object_global_index_data
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet) :
    CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
      IsPrimePow
      (fun n =>
        base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest)) n where
  primePowerIndex :=
    (data.common_route_visible_atom_data lambda hlambda
      (data.common_finite_prime_concrete_object_global_visible
        lambda hlambda hn)).primePowerIndex
  atomVisible :=
    (data.common_route_visible_atom_data lambda hlambda
      (data.common_finite_prime_concrete_object_global_visible
        lambda hlambda hn)).atomVisible

theorem common_finite_prime_concrete_object_restricted_visible
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda) :
    base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
      (base.ccm25Model.toWeilFormSymbols.convolutionStar
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest) := by
  have hvisible :
      (data.commonFinitePrimeConcreteObject
        lambda hlambda).sourceTest.sourceAtomVisible n :=
    CCM25Concrete.FinitePrimeCertificate.concrete_object_restricted_index_visible
      (data.commonFinitePrimeConcreteObject lambda hlambda) hn
  have hcommon : data.concreteCommonTest.sourceAtomVisible n := by
    simpa [data.common_finite_prime_concrete_object_source_test_eq_concrete
      lambda hlambda] using hvisible
  exact (data.concreteCommonTest.route_visibility_iff_source_visibility n).2 hcommon

theorem common_finite_prime_concrete_object_restricted_index_data
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda) :
    CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
      IsPrimePow
      (fun n =>
        base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest)) lambda n where
  primePowerIndex :=
    (data.common_route_visible_atom_data lambda hlambda
      (data.common_finite_prime_concrete_object_restricted_visible
        lambda hlambda hn)).primePowerIndex
  atomVisible :=
    (data.common_route_visible_atom_data lambda hlambda
      (data.common_finite_prime_concrete_object_restricted_visible
        lambda hlambda hn)).atomVisible
  lambdaCut :=
    CCM25Concrete.FinitePrimeCertificate.concrete_object_restricted_index_lambda_cut
      (data.commonFinitePrimeConcreteObject lambda hlambda) hn

theorem common_finite_prime_concrete_object_restricted_index_one_lt
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda) :
    1 < n :=
  CCM25Concrete.PrimePowerSupport.source_lambda_cut_one_lt
    (data.common_finite_prime_concrete_object_restricted_index_data
      lambda hlambda hn).lambdaCut

theorem common_finite_prime_concrete_object_restricted_index_le_lambda_sq
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  CCM25Concrete.PrimePowerSupport.source_lambda_cut_le_lambda_sq
    (data.common_finite_prime_concrete_object_restricted_index_data
      lambda hlambda hn).lambdaCut

theorem common_restricted_index_set_eq_global
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda =
      base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet :=
  CCM25Concrete.FinitePrimeCertificate.restricted_index_set_eq_global_of_arithmetic_certificate
    (data.commonArithmeticCertificate lambda hlambda)

theorem common_finite_prime_visibility_at_lambda
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeExact.FinitePrimeVisibilityAtLambdaStatement
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda :=
  CCM25Concrete.FinitePrimeExact.visibility_at_lambda_of_exact_support
    (CCM25Concrete.FinitePrimeCertificate.exact_support_of_arithmetic_certificate
      (data.commonArithmeticCertificate lambda hlambda))

theorem common_global_finite_prime_term_sum_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) =
      CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest
        (CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
          (data.commonArithmeticCertificate lambda hlambda)) := by
  calc
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) =
        CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest
          (data.commonArithmeticCertificate lambda hlambda).atoms :=
      CCM25Concrete.FinitePrimeCertificate.concrete_object_global_finite_prime_term_sum_read_off
        (data.commonFinitePrimeConcreteObject lambda hlambda)
    _ =
        CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest
          (CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
            (data.commonArithmeticCertificate lambda hlambda)) :=
      (PrimePowerArithmetic.source_global_finite_prime_evaluator_sum_on_index_set_of_global
        (data.commonArithmeticCertificate lambda hlambda).atoms).symm

theorem common_global_von_mangoldt_pairing_sum_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest
        (CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
          (data.commonArithmeticCertificate lambda hlambda)) := by
  calc
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
        CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest
          (data.commonArithmeticCertificate lambda hlambda).atoms :=
      CCM25Concrete.FinitePrimeCertificate.concrete_object_global_von_mangoldt_pairing_sum_read_off
        (data.commonFinitePrimeConcreteObject lambda hlambda)
    _ =
        CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest
          (CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
            (data.commonArithmeticCertificate lambda hlambda)) :=
      (PrimePowerArithmetic.source_global_finite_prime_evaluator_sum_on_index_set_of_global
        (data.commonArithmeticCertificate lambda hlambda).atoms).symm

theorem common_psi_scoped_source_evaluator_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    base.ccm25Model.toWeilFormSymbols.psi
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
            (data.commonArithmeticPackage lambda hlambda) :=
  CCM25Concrete.Package.psi_scoped_source_evaluator_common_atoms_of_package
    (data.commonArithmeticPackage lambda hlambda)

theorem common_qw_scoped_source_evaluator_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    base.ccm25Model.toWeilFormSymbols.qw
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
            (data.commonArithmeticPackage lambda hlambda) :=
  CCM25Concrete.Package.qw_scoped_source_evaluator_common_atoms_of_package
    (data.commonArithmeticPackage lambda hlambda)

theorem common_restricted_finite_prime_term_sum_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) =
      CCM25Concrete.PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest lambda
        (data.commonArithmeticCertificate lambda hlambda).atoms :=
  CCM25Concrete.FinitePrimeCertificate.concrete_object_restricted_finite_prime_term_sum_read_off
    (data.commonFinitePrimeConcreteObject lambda hlambda)

theorem common_restricted_von_mangoldt_pairing_sum_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      CCM25Concrete.PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest lambda
        (data.commonArithmeticCertificate lambda hlambda).atoms :=
  CCM25Concrete.FinitePrimeCertificate.concrete_object_restricted_von_mangoldt_pairing_sum_read_off
    (data.commonFinitePrimeConcreteObject lambda hlambda)

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        (data.toSourceObjectCommonData).concreteArithmeticRows
        (data.toSourceObjectCommonData).commonTest.sourceTest
        (data.toSourceObjectCommonData).commonTest.sourceTest :=
  (data.toSourceObjectCommonData).ccm25Test_eq_commonTest

def commonFinitePrimeArithmeticSourceData
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      base.ccm25Model.toWeilFormSymbols :=
  CCM25Concrete.FinitePrimeSourceData.commonFinitePrimeArithmeticSourceDataOfArithmeticRows
    data.concreteCommonTest.sourceTest
    data.concreteArithmeticRows
    data.arithmeticRowsUseConcreteCommonTest
    data.scopedArchimedeanContributionBalance

theorem common_finite_prime_source_test_pair_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.commonFinitePrimeArithmeticSourceData.finitePrimeData.selector.sourceTest
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest) =
      data.concreteCommonTest.toSourceTestEvaluationInterface :=
  CCM25Concrete.FinitePrimeSourceData.commonPairSourceTest
    data.commonFinitePrimeArithmeticSourceData

theorem common_finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      base.ccm25Model.toWeilFormSymbols :=
  CCM25Concrete.FinitePrimeInterface.finite_prime_normalization_of_source_test_certificates
    (CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      data.commonFinitePrimeArithmeticSourceData)

theorem common_finite_prime_term_normalization
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest :=
  (data.common_finite_prime_normalization
    data.concreteCommonTest.sourceTest
    data.concreteCommonTest.sourceTest).finitePrimeTermNormalization

theorem common_data_finite_prime_normalization_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).finitePrimeNormalization =
      data.common_finite_prime_normalization :=
  rfl

end SourceObjectConcreteCommonData

namespace SourceObjectCommonData

def toCCM25WeilObjectPackage
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    SourceObject.CCM25WeilObjectPackage where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows := common.concreteArithmeticRows

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        common.concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  common.ccm25Test_eq_commonTest

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      base.ccm25Model.toWeilFormSymbols :=
  common.finitePrimeNormalization

theorem finite_prime_term_normalization
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      base.ccm25Model.toWeilFormSymbols common.commonTest.sourceTest
      common.commonTest.sourceTest :=
  (common.finite_prime_normalization common.commonTest.sourceTest
    common.commonTest.sourceTest).finitePrimeTermNormalization

def toFinitePrimeTheoremBase
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBaseFinitePrime where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows := common.concreteArithmeticRows
  finitePrimeNormalization := common.finite_prime_normalization

def toPartialQWFinitePrime
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBasePartialQWFinitePrime where
  sourceModel := base.ccm25Model
  concreteArithmeticRows := common.concreteArithmeticRows
  qwDefinition := base.toCCM25TheoremBase.qwDefinition
  finitePrimeNormalization := common.finite_prime_normalization

def toCCM25TheoremBaseWithConcreteFinitePrime
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBase where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  qwDefinition := base.toCCM25TheoremBase.qwDefinition
  psiSign := base.toCCM25TheoremBase.psiSign
  qwLambdaFormula := base.toCCM25TheoremBase.qwLambdaFormula
  finitePrimeNormalization := common.finite_prime_normalization
  poleNormalization := base.toCCM25TheoremBase.poleNormalization
  noSpectralShortcutImport := ccm25_no_spectral_shortcut_import

theorem toCCM25WeilObjectPackage_rows_eq
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    (common.toCCM25WeilObjectPackage).concreteArithmeticRows =
      common.concreteArithmeticRows :=
  rfl

theorem toCCM25WeilObjectPackage_symbols_eq
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    (common.toCCM25WeilObjectPackage).weilSymbols =
      base.ccm25Model.toWeilFormSymbols :=
  rfl

end SourceObjectCommonData

/--
Expanded row data after Goal 2C.

The CCM25 row is intentionally not a free field: it is computed from
`SourceObjectCommonData`, which already ties the arithmetic rows to the common
source test and the Goal 0E finite-prime theorem path.
-/
structure SourceObjectExpandedRows
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base) where
  ccm24 : SourceObject.CCM24SemilocalObjectPackage
  cc20Trace : SourceObject.CC20TraceObjectPackage
  cc20SupportSquareComparison :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison cc20Trace

namespace SourceObjectExpandedRows

open CC20Concrete.TraceScale

abbrev CC20SupportSquareComparison :=
  CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison

abbrev CC20ScalarSupportSquareComparison :=
  CC20Concrete.TraceScale.CC20TracePackageScalarSupportSquareComparison

def normalizedCC20SupportSquareComparison
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    CC20SupportSquareComparison
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders) :=
  CC20TracePackageSupportSquareComparison.forNormalizedSeedTraceObjectPackage
    normalizedSeed remainders

noncomputable def normalizedScalarCC20SupportSquareComparison
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    CC20SupportSquareComparison
      (CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
        scalarSeed remainders) where
  normalizedSeed :=
    CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed scalarSeed
  remainders := remainders
  supportSquareTrace_eq := by
    apply heq_of_eq
    funext g
    exact
      CC20Concrete.TraceScale.normalized_scalar_as_legal_square_seed_support_square_eq_scalar
        scalarSeed g

noncomputable def normalizedScalarCC20ScalarSupportSquareComparison
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    CC20ScalarSupportSquareComparison
      (CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
        scalarSeed remainders) :=
  open CC20Concrete.TraceScale.CC20TracePackageScalarSupportSquareComparison in
    forNormalizedScalarTraceObjectPackage scalarSeed remainders

def ofNormalizedCC20Trace
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    SourceObjectExpandedRows base common where
  ccm24 := ccm24
  cc20Trace :=
    CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      normalizedSeed remainders
  cc20SupportSquareComparison :=
    normalizedCC20SupportSquareComparison normalizedSeed remainders

noncomputable def ofNormalizedScalarCC20Trace
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    SourceObjectExpandedRows base common where
  ccm24 := ccm24
  cc20Trace :=
    CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
      scalarSeed remainders
  cc20SupportSquareComparison :=
    normalizedScalarCC20SupportSquareComparison scalarSeed remainders

theorem of_normalized_cc20_trace_cc20_trace_eq
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    (ofNormalizedCC20Trace (base := base) (common := common)
      ccm24 normalizedSeed remainders).cc20Trace =
      CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders :=
  rfl

theorem of_normalized_scalar_cc20_trace_cc20_trace_eq
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    (ofNormalizedScalarCC20Trace (base := base) (common := common)
      ccm24 scalarSeed remainders).cc20Trace =
      CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
        scalarSeed remainders :=
  rfl

theorem of_normalized_cc20_trace_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    (ofNormalizedCC20Trace (base := base) (common := common)
      ccm24 normalizedSeed remainders).cc20SupportSquareComparison =
      normalizedCC20SupportSquareComparison normalizedSeed remainders :=
  rfl

theorem of_normalized_scalar_cc20_trace_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    (ofNormalizedScalarCC20Trace (base := base) (common := common)
      ccm24 scalarSeed remainders).cc20SupportSquareComparison =
      normalizedScalarCC20SupportSquareComparison scalarSeed remainders :=
  rfl

def ccm25
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    SourceObject.CCM25WeilObjectPackage :=
  common.toCCM25WeilObjectPackage

theorem ccm25_rows_eq_common_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    rows.ccm25.concreteArithmeticRows = common.concreteArithmeticRows :=
  rfl

theorem ccm25_symbols_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    rows.ccm25.weilSymbols = base.ccm25Model.toWeilFormSymbols :=
  rfl

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        (ccm25 _rows).concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  common.ccm25Test_eq_commonTest

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      (ccm25 _rows).weilSymbols :=
  common.finite_prime_normalization

def cc20_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      rows.cc20Trace :=
  rows.cc20SupportSquareComparison

theorem cc20_support_square_existing_identification
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectArchimedeanSymbols
          rows.cc20SupportSquareComparison.normalizedSeed
          rows.cc20SupportSquareComparison.remainders))
      rows.cc20Trace.archimedeanSymbols.supportSquareTrace :=
  rows.cc20SupportSquareComparison.supportSquareTrace_eq

def toPartialQWFinitePrime
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    CCM25TheoremBasePartialQWFinitePrime :=
  common.toPartialQWFinitePrime

end SourceObjectExpandedRows

/--
Cross-object bridge data needed to assemble a `SourceObjectPackage`.

The bridge keeps the remaining mixed-row obligations explicit: common-test
involution, CCM24/CC20 common-test ownership, window controls, finite-prime
support matching, final sign compatibility, and the RH-exit bridge used by the
expanded CC20 exit object.
-/
structure SourceObjectCrossObjectBridges
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (rows : SourceObjectExpandedRows base common)
    (rhExit : SourceObject.CC20RHExitObjectPackage) where
  rhDefinitionBridge_eq_base :
    rhExit.rhDefinitionBridge = base.rhDefinitionBridge
  commonTestInvolution :
    SourceObject.CommonTestInvolutionBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols common.commonTest
  ccm24Test_eq_commonTest :
    SourceObject.CCM24CommonTestBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols
      common.commonTest rows.ccm24
  cc20TraceTest_eq_commonTest :
    SourceObject.CC20CommonTestBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols
      common.commonTest rows.cc20Trace
  convolutionSquare_eq_Fg : Prop
  ccm24Window_controls_qwLambda : Prop
  ccm24Window_controls_cdef : Prop
  finitePrimeSupport_matches_window : Prop
  qW_sign_bridge : Prop

namespace SourceObjectCrossObjectBridges

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (_bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        (SourceObjectExpandedRows.ccm25 rows).concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows

theorem rh_definition_bridge_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    rhExit.rhDefinitionBridge = base.rhDefinitionBridge :=
  bridges.rhDefinitionBridge_eq_base

end SourceObjectCrossObjectBridges

/--
Goal 2D constructor for the expanded source-object package.

Every field is supplied by the staged base package, common-test data, expanded
rows, explicit RH-exit object, or named cross-object bridge data.  This is not
a no-argument source package and does not prove the remaining analytic rows.
-/
def sourceObjectPackageOfData
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (rows : SourceObjectExpandedRows base common)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    SourceObject.SourceObjectPackage where
  ccm24 := rows.ccm24
  ccm25 := SourceObjectExpandedRows.ccm25 rows
  commonTest := common.commonTest
  cc20Trace := rows.cc20Trace
  cc20RHExit := rhExit
  commonTestInvolution := bridges.commonTestInvolution
  ccm24Test_eq_commonTest := bridges.ccm24Test_eq_commonTest
  ccm25Test_eq_commonTest :=
    SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows
  cc20TraceTest_eq_commonTest := bridges.cc20TraceTest_eq_commonTest
  convolutionSquare_eq_Fg := bridges.convolutionSquare_eq_Fg
  ccm24Window_controls_qwLambda := bridges.ccm24Window_controls_qwLambda
  ccm24Window_controls_cdef := bridges.ccm24Window_controls_cdef
  finitePrimeSupport_matches_window := bridges.finitePrimeSupport_matches_window
  qW_sign_bridge := bridges.qW_sign_bridge

def sourceObjectPackageOfNormalizedCC20Trace
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfData base common
    (SourceObjectExpandedRows.ofNormalizedCC20Trace
      ccm24 normalizedSeed remainders)
    rhExit bridges

noncomputable def sourceObjectPackageOfNormalizedScalarCC20Trace
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfData base common
    (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
      ccm24 scalarSeed remainders)
    rhExit bridges

/--
Source-object input for the normalized CC20 trace package.

This is the boundary where the compact theorem-base package becomes a full
source-object package: the CCM24 object, RH-exit object, and cross-object
bridges must be supplied together for the same normalized seed and remainder
data.
-/
structure NormalizedCC20SourceObjectLayerInput
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed) where
  ccm24 : SourceObject.CCM24SemilocalObjectPackage
  rhExit : SourceObject.CC20RHExitObjectPackage
  bridges :
    SourceObjectCrossObjectBridges base common
      (SourceObjectExpandedRows.ofNormalizedCC20Trace
        ccm24 normalizedSeed remainders)
      rhExit

namespace NormalizedCC20SourceObjectLayerInput

def rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols}
    {remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed}
    (input :
      NormalizedCC20SourceObjectLayerInput
        base common normalizedSeed remainders) :
    SourceObjectExpandedRows base common :=
  SourceObjectExpandedRows.ofNormalizedCC20Trace
    input.ccm24 normalizedSeed remainders

def package
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols}
    {remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed}
    (input :
      NormalizedCC20SourceObjectLayerInput
        base common normalizedSeed remainders) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfNormalizedCC20Trace
    base common input.ccm24 normalizedSeed remainders input.rhExit
    input.bridges

end NormalizedCC20SourceObjectLayerInput

/--
Source-object input for the scalar normalized CC20 trace package.

The scalar package reuses the same base/common/CCM24 objects but has its own
scalar CC20 trace object, RH-exit object, and bridge package.
-/
structure NormalizedScalarSourceObjectLayerInput
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) where
  rhExit : SourceObject.CC20RHExitObjectPackage
  bridges :
    SourceObjectCrossObjectBridges base common
      (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
        ccm24 scalarSeed remainders)
      rhExit

namespace NormalizedScalarSourceObjectLayerInput

noncomputable def rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {ccm24 : SourceObject.CCM24SemilocalObjectPackage}
    {scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols}
    {remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)}
    (_input :
      NormalizedScalarSourceObjectLayerInput
        base common ccm24 scalarSeed remainders) :
    SourceObjectExpandedRows base common :=
  SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
    ccm24 scalarSeed remainders

noncomputable def package
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {ccm24 : SourceObject.CCM24SemilocalObjectPackage}
    {scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols}
    {remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)}
    (input :
      NormalizedScalarSourceObjectLayerInput
        base common ccm24 scalarSeed remainders) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfNormalizedScalarCC20Trace
    base common ccm24 scalarSeed remainders input.rhExit input.bridges

end NormalizedScalarSourceObjectLayerInput

namespace SourceObjectPackageOfData

theorem normalized_cc20_trace_package_eq_data_constructor
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges =
      sourceObjectPackageOfData base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit bridges :=
  rfl

theorem normalized_cc20_trace_package_cc20_trace_eq
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    (sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace =
      CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders :=
  rfl

theorem normalized_scalar_cc20_trace_package_cc20_trace_eq
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    (sourceObjectPackageOfNormalizedScalarCC20Trace
      base common ccm24 scalarSeed remainders rhExit bridges).cc20Trace =
      CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
        scalarSeed remainders :=
  rfl

def normalized_seed_ordinary_trace_support_square_statement
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols :=
  normalizedSeed.ordinary_trace_support_square_statement

def normalized_seed_support_square_no_defect_statement
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols) :
    ∀ g :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols.Test,
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols.traceClass g →
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols.cyclicLegal g →
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols.supportSquareTrace g =
        (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          normalizedSeed).archimedeanSymbols.sourceNoDefectTrace g :=
  CC20Concrete.TraceScale.ConcreteTraceScaleSymbols.support_square_no_defect_statement
    (CC20Concrete.TraceScale.normalizedSeedConcreteSymbols normalizedSeed)

theorem normalized_cc20_trace_package_ordinary_trace_support_square
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols
        (sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  normalized_seed_ordinary_trace_support_square_statement normalizedSeed

theorem normalized_cc20_trace_package_support_square_no_defect
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    let A :=
      SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols
        (sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    ∀ g : A.Test, A.traceClass g → A.cyclicLegal g →
      A.supportSquareTrace g = A.sourceNoDefectTrace g :=
  normalized_seed_support_square_no_defect_statement normalizedSeed

theorem normalized_scalar_cc20_trace_package_source_no_defect_eq_scalar
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (g : scalarSeed.Test) :
    let pkg :=
      sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges
    pkg.cc20Trace.archimedeanSymbols.sourceNoDefectTrace g =
      scalarSeed.scalarTrace g := by
  intro pkg
  rfl

theorem normalized_scalar_cc20_trace_package_support_square_eq_scalar
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (g : scalarSeed.Test) :
    let pkg :=
      sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges
    pkg.cc20Trace.archimedeanSymbols.supportSquareTrace g =
      scalarSeed.scalarTrace g := by
  intro pkg
  rfl

theorem normalized_scalar_cc20_trace_package_support_square_no_defect
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    let A :=
      SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols
        (sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges)
    ∀ g : A.Test, A.traceClass g → A.cyclicLegal g →
      A.supportSquareTrace g = A.sourceNoDefectTrace g := by
  intro A g _htrace _hcyclic
  rfl

def normalized_cc20_trace_package_support_square_comparison
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      (sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace :=
  SourceObjectExpandedRows.cc20SupportSquareComparison
    (SourceObjectExpandedRows.ofNormalizedCC20Trace
      (base := base) (common := common) ccm24 normalizedSeed remainders)

noncomputable def normalized_scalar_cc20_trace_package_support_square_comparison
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      (sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges).cc20Trace :=
  SourceObjectExpandedRows.cc20SupportSquareComparison
    (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
      (base := base) (common := common) ccm24 scalarSeed remainders)

noncomputable def normalized_scalar_cc20_trace_package_scalar_support_square_comparison
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (_bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageScalarSupportSquareComparison
      (sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit _bridges).cc20Trace :=
  SourceObjectExpandedRows.normalizedScalarCC20ScalarSupportSquareComparison
    scalarSeed remainders

theorem ccm25_eq_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).ccm25 =
      SourceObjectExpandedRows.ccm25 rows :=
  rfl

theorem commonTest_eq_common
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).commonTest =
      common.commonTest :=
  rfl

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).ccm25Test_eq_commonTest =
      SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows :=
  rfl

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      (sourceObjectPackageOfData base common rows rhExit bridges).ccm25.weilSymbols :=
  SourceObjectExpandedRows.finite_prime_normalization rows

def cc20_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      (sourceObjectPackageOfData base common rows rhExit bridges).cc20Trace :=
  rows.cc20SupportSquareComparison

theorem cc20_support_square_existing_identification
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectArchimedeanSymbols
          rows.cc20SupportSquareComparison.normalizedSeed
          rows.cc20SupportSquareComparison.remainders))
      (ArchimedeanTraceSymbols.supportSquareTrace
        (SourceObject.CC20TraceObjectPackage.archimedeanSymbols
          (SourceObject.SourceObjectPackage.cc20Trace
            (sourceObjectPackageOfData base common rows rhExit bridges)))) :=
  SourceObjectExpandedRows.cc20_support_square_existing_identification rows

theorem rh_definition_bridge_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).cc20RHExit.rhDefinitionBridge =
      base.rhDefinitionBridge :=
  bridges.rhDefinitionBridge_eq_base

end SourceObjectPackageOfData

end Source
end ConnesWeilRH
