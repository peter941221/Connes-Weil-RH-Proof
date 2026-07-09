/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25
import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CCM25Concrete.Interface
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
import ConnesWeilRH.Source.CCM25SourceModel
import ConnesWeilRH.Source.Objects

/-!
# CCM25 Lean theorem base

This module gives Goal 1 a Lean-checkable CCM25 theorem-base layer.  The
theorems are stated over concrete Weil-form symbols and avoid
`SourceObligation.Holds` and reviewer-decision inputs.
-/

namespace ConnesWeilRH
namespace Source

/-- Negative boundary: the scalar route does not import CCM25 spectral data. -/
def CCM25SpectralShortcutImported : Prop := False

theorem ccm25_no_spectral_shortcut_import :
    ¬ CCM25SpectralShortcutImported := by
  intro h
  exact h

/--
Constructor-facing CCM25 source arithmetic data.

This is the non-circular source boundary for a future CCM25 formal/import pass:
it stores the source-facing Weil symbols together with the four concrete row
families that are exactly needed to build `ConcreteCCM25ArithmeticRows`.  It
does not depend on `SourceObjectPackage`, route certificates, ledgers, or any
downstream RH endpoint.
-/
structure CCM25SourceArithmeticConstructorInput where
  weilSymbols : WeilFormSymbols
  globalRows : CCM25Concrete.Rows.ConcreteGlobalQWPsiRows weilSymbols
  restrictedRows : CCM25Concrete.Rows.ConcreteRestrictedQWLambdaRows weilSymbols
  finitePrimeArithmeticSourceData :
    CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      weilSymbols
  poleRows : CCM25Concrete.Rows.ConcretePoleNormalizationRows weilSymbols

namespace CCM25SourceArithmeticConstructorInput

def toConcreteArithmeticRows
    (input : CCM25SourceArithmeticConstructorInput) :
    CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows input.weilSymbols where
  globalRows := input.globalRows
  restrictedRows := input.restrictedRows
  finitePrimeArithmeticCertificates :=
    CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      input.finitePrimeArithmeticSourceData
  poleRows := input.poleRows

def toCCM25WeilObjectPackage
    (input : CCM25SourceArithmeticConstructorInput) :
    SourceObject.CCM25WeilObjectPackage where
  weilSymbols := input.weilSymbols
  concreteArithmeticRows := input.toConcreteArithmeticRows

noncomputable def toCCM25SourceModel
    (input : CCM25SourceArithmeticConstructorInput) :
    CCM25SourceModel :=
  ccm25_source_model_of_arithmetic_rows input.toConcreteArithmeticRows

@[simp]
theorem toCCM25WeilObjectPackage_symbols
    (input : CCM25SourceArithmeticConstructorInput) :
    input.toCCM25WeilObjectPackage.weilSymbols = input.weilSymbols :=
  rfl

@[simp]
theorem toCCM25WeilObjectPackage_rows
    (input : CCM25SourceArithmeticConstructorInput) :
    input.toCCM25WeilObjectPackage.concreteArithmeticRows =
      input.toConcreteArithmeticRows :=
  rfl

@[simp]
theorem toCCM25SourceModel_toWeilFormSymbols
    (input : CCM25SourceArithmeticConstructorInput) :
    input.toCCM25SourceModel.toWeilFormSymbols = input.weilSymbols := by
  simp [toCCM25SourceModel, toConcreteArithmeticRows,
    ccm25_source_model_of_arithmetic_rows_to_weil_form_symbols]

theorem qw_definition
    (input : CCM25SourceArithmeticConstructorInput) :
    WeilFormSymbols.QWDefinitionStatement input.weilSymbols :=
  CCM25Concrete.Rows.qw_definition_of_arithmetic_rows
    input.toConcreteArithmeticRows

theorem psi_sign
    (input : CCM25SourceArithmeticConstructorInput) :
    WeilFormSymbols.PsiSignStatement input.weilSymbols :=
  CCM25Concrete.Rows.psi_sign_of_arithmetic_rows
    input.toConcreteArithmeticRows

theorem qw_lambda_formula
    (input : CCM25SourceArithmeticConstructorInput) :
    WeilFormSymbols.QWLambdaFormulaStatement input.weilSymbols :=
  CCM25Concrete.Rows.qw_lambda_formula_of_arithmetic_rows
    input.toConcreteArithmeticRows

theorem finite_prime_normalization
    (input : CCM25SourceArithmeticConstructorInput) :
    WeilFormSymbols.FinitePrimeNormalizationStatement input.weilSymbols :=
  CCM25Concrete.FinitePrimeInterface.finite_prime_normalization_of_common_source_test_certificates
    (CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      input.finitePrimeArithmeticSourceData)

theorem pole_normalization
    (input : CCM25SourceArithmeticConstructorInput) :
    WeilFormSymbols.PoleNormalizationStatement input.weilSymbols :=
  CCM25Concrete.Rows.pole_normalization_of_arithmetic_rows
    input.toConcreteArithmeticRows

end CCM25SourceArithmeticConstructorInput

namespace AnalyticCore

noncomputable def SourceWeilFormData.toCCM25SourceArithmeticConstructorInput
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (finitePrimeArithmeticSourceData :
      CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        W.toWeilFormSymbols) :
    CCM25SourceArithmeticConstructorInput where
  weilSymbols := W.toWeilFormSymbols
  globalRows :=
    { qwDefinition := W.qw_definition_statement
      psiSign := W.psi_sign_statement }
  restrictedRows :=
    { qwLambdaFormula := W.qw_lambda_formula_statement }
  finitePrimeArithmeticSourceData := finitePrimeArithmeticSourceData
  poleRows :=
    { poleNormalization := W.pole_normalization_statement }

end AnalyticCore

/-- Data-bearing Lean theorem base for the CCM25 source-interface row. -/
structure CCM25TheoremBase where
  weilSymbols : WeilFormSymbols
  qwDefinition : WeilFormSymbols.QWDefinitionStatement weilSymbols
  psiSign : WeilFormSymbols.PsiSignStatement weilSymbols
  qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement weilSymbols
  finitePrimeNormalization :
    WeilFormSymbols.FinitePrimeNormalizationStatement weilSymbols
  poleNormalization : WeilFormSymbols.PoleNormalizationStatement weilSymbols
  noSpectralShortcutImport : ¬ CCM25SpectralShortcutImported

namespace CCM25TheoremBase

noncomputable def ofSourceArithmeticConstructorInput
    (input : CCM25SourceArithmeticConstructorInput) :
    CCM25TheoremBase where
  weilSymbols := input.weilSymbols
  qwDefinition := input.qw_definition
  psiSign := input.psi_sign
  qwLambdaFormula := input.qw_lambda_formula
  finitePrimeNormalization := input.finite_prime_normalization
  poleNormalization := input.pole_normalization
  noSpectralShortcutImport := ccm25_no_spectral_shortcut_import

def discharged (M : CCM25SourceModel) : CCM25TheoremBase where
  weilSymbols := M.toWeilFormSymbols
  qwDefinition := ccm25_source_qw_definition M
  psiSign := ccm25_source_psi_sign M
  qwLambdaFormula := ccm25_source_qw_lambda_formula M
  finitePrimeNormalization := ccm25_source_finite_prime_normalization M
  poleNormalization := ccm25_source_pole_normalization M
  noSpectralShortcutImport := ccm25_no_spectral_shortcut_import

noncomputable def dischargedWithConcreteFinitePrime
    (M : CCM25SourceModel)
    (hfinite :
      CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows M.toWeilFormSymbols) :
    CCM25TheoremBase where
  weilSymbols := M.toWeilFormSymbols
  qwDefinition := ccm25_source_qw_definition M
  psiSign := ccm25_source_psi_sign M
  qwLambdaFormula := ccm25_source_qw_lambda_formula M
  finitePrimeNormalization :=
    CCM25Concrete.FinitePrimeInterface.finite_prime_normalization_of_common_source_test_certificates
        hfinite.finitePrimeArithmeticCertificates
  poleNormalization := ccm25_source_pole_normalization M
  noSpectralShortcutImport := ccm25_no_spectral_shortcut_import

def toInterface (h : CCM25TheoremBase) : CCM25Interface where
  weilSymbols := h.weilSymbols
  qwDefinition := h.qwDefinition
  psiSign := h.psiSign
  qwLambdaFormula := h.qwLambdaFormula
  finitePrimeNormalization := h.finitePrimeNormalization
  poleNormalization := h.poleNormalization

end CCM25TheoremBase

/--
Partial Goal 1B discharge for CCM25: only the global `QW(f,g)=Psi(f^* * g)`
field has been proved from a source model.  The other CCM25 theorem-base fields
remain open.
-/
structure CCM25TheoremBasePartialQW where
  sourceModel : CCM25SourceModel
  qwDefinition :
    WeilFormSymbols.QWDefinitionStatement sourceModel.toWeilFormSymbols

namespace CCM25TheoremBasePartialQW

def ofSourceModel (M : CCM25SourceModel) : CCM25TheoremBasePartialQW where
  sourceModel := M
  qwDefinition := ccm25_source_qw_definition M

end CCM25TheoremBasePartialQW

/--
Goal 0E discharge for the CCM25 finite-prime row.

This is narrower than a full `CCM25TheoremBase`: it replaces the
`CCM25SourceModel.finitePrimeNormalization` law-field projection with the
finite-prime normalization theorem assembled from source-test arithmetic
certificate owners.
-/
structure CCM25TheoremBaseFinitePrime where
  weilSymbols : WeilFormSymbols
  finitePrimeArithmeticSourceTestCertificates :
    CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      weilSymbols
  finitePrimeNormalization :
    WeilFormSymbols.FinitePrimeNormalizationStatement weilSymbols

namespace CCM25TheoremBaseFinitePrime

end CCM25TheoremBaseFinitePrime

/--
Partial CCM25 theorem-base slice after Goal 0E.

The `QW` field still comes from the current source-model staging layer, while
finite-prime normalization is supplied by source-test arithmetic certificate
owners instead of `CCM25SourceModel` law fields.
-/
structure CCM25TheoremBasePartialQWFinitePrime where
  sourceModel : CCM25SourceModel
  finitePrimeArithmeticSourceTestCertificates :
    CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
        sourceModel.toWeilFormSymbols
  qwDefinition :
    WeilFormSymbols.QWDefinitionStatement sourceModel.toWeilFormSymbols
  finitePrimeNormalization :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      sourceModel.toWeilFormSymbols

namespace CCM25TheoremBasePartialQWFinitePrime

end CCM25TheoremBasePartialQWFinitePrime

end Source
end ConnesWeilRH
