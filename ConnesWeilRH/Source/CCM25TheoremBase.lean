/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25
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

end Source
end ConnesWeilRH
