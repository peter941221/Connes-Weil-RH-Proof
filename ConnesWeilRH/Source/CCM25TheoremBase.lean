/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25
import ConnesWeilRH.Source.CCM25Concrete.Interface
import ConnesWeilRH.Source.CCM25SourceModel

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
    CCM25Concrete.Interface.finite_prime_normalization_of_arithmetic_rows
      hfinite
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

theorem ccm25_finite_prime_normalization_of_concrete_arithmetic_rows
    {W : WeilFormSymbols}
    (h : CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  CCM25Concrete.Interface.finite_prime_normalization_of_arithmetic_rows h

/--
Goal 0E discharge for the CCM25 finite-prime row.

This is narrower than a full `CCM25TheoremBase`: it replaces the
`CCM25SourceModel.finitePrimeNormalization` law-field projection with the
finite-prime normalization theorem assembled from concrete arithmetic rows.
-/
structure CCM25TheoremBaseFinitePrime where
  weilSymbols : WeilFormSymbols
  concreteArithmeticRows :
    CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows weilSymbols
  finitePrimeNormalization :
    WeilFormSymbols.FinitePrimeNormalizationStatement weilSymbols

namespace CCM25TheoremBaseFinitePrime

noncomputable def ofArithmeticRows
    {W : WeilFormSymbols}
    (h : CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows W) :
    CCM25TheoremBaseFinitePrime where
  weilSymbols := W
  concreteArithmeticRows := h
  finitePrimeNormalization :=
    CCM25Concrete.Interface.finite_prime_normalization_of_arithmetic_rows h

theorem finite_prime_normalization_of_arithmetic_rows
    {W : WeilFormSymbols}
    (h : CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows W) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W :=
  (ofArithmeticRows h).finitePrimeNormalization

end CCM25TheoremBaseFinitePrime

/--
Partial CCM25 theorem-base slice after Goal 0E.

The `QW` field still comes from the current source-model staging layer, while
finite-prime normalization is supplied by concrete arithmetic rows instead of
`CCM25SourceModel` law fields.
-/
structure CCM25TheoremBasePartialQWFinitePrime where
  sourceModel : CCM25SourceModel
  concreteArithmeticRows :
    CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      sourceModel.toWeilFormSymbols
  qwDefinition :
    WeilFormSymbols.QWDefinitionStatement sourceModel.toWeilFormSymbols
  finitePrimeNormalization :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      sourceModel.toWeilFormSymbols

namespace CCM25TheoremBasePartialQWFinitePrime

noncomputable def ofSourceModelAndArithmeticRows
    (M : CCM25SourceModel)
    (hfinite :
      CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows M.toWeilFormSymbols) :
    CCM25TheoremBasePartialQWFinitePrime where
  sourceModel := M
  concreteArithmeticRows := hfinite
  qwDefinition := ccm25_source_qw_definition M
  finitePrimeNormalization :=
    ccm25_finite_prime_normalization_of_concrete_arithmetic_rows hfinite

end CCM25TheoremBasePartialQWFinitePrime

end Source
end ConnesWeilRH
