/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.Rows

/-!
# CCM25 source model

This module starts the Goal 1B field-by-field discharge path for CCM25. The
first discharged field is the source-model read-off

```text
QW(f,g) = Psi(f^* * g).
```

The remaining Weil-form symbols stay explicit model data plus explicit model
laws. They are not filled with zero, empty support, or toy formulas in this
module.
-/

namespace ConnesWeilRH
namespace Source

/--
Source-facing CCM25 data at the current phase-1 `TestFunction := Type`
boundary.

The source model owns `qw`, `psi`, and the convolution-square operation, plus
the laws tying the Weil-form fields together. These laws are the current Lean
source-model boundary for Goal 1B; they are not `SourceObligation` metadata.
-/
structure CCM25SourceModel where
  qw : TestFunction → TestFunction → ℝ
  convolutionStar : TestFunction → TestFunction → TestFunction
  psi : TestFunction → ℝ
  qwLambda : ℝ → TestFunction → TestFunction → ℝ
  globalPrimeIndexSet : Finset ℕ
  restrictedPrimeIndexSet : ℝ → Finset ℕ
  finitePrimeAtomVisible : ℕ → TestFunction → Prop
  finitePrimeTerm : ℕ → TestFunction → ℝ
  archimedeanTerm : TestFunction → ℝ
  poleFunctional : TestFunction → ℝ
  polePairing : TestFunction → ℝ
  primePowerPairing : ℕ → TestFunction → TestFunction → ℝ
  vonMangoldtWeight : ℕ → ℝ
  qw_eq_psi_convolution :
    ∀ f g : TestFunction, qw f g = psi (convolutionStar f g)
  psi_sign_formula :
    ∀ F : TestFunction,
      psi F =
        poleFunctional F - archimedeanTerm F -
          ∑ n ∈ globalPrimeIndexSet, finitePrimeTerm n F
  qw_lambda_formula :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ f : TestFunction,
        qwLambda lambda f f =
          archimedeanTerm (convolutionStar f f) +
            polePairing f -
              ∑ n ∈ restrictedPrimeIndexSet lambda,
                vonMangoldtWeight n * primePowerPairing n f f
  global_prime_index_coverage :
    ∀ f g : TestFunction,
      WeilFormSymbols.GlobalPrimeIndexCoverageStatement
        { qw := qw
          qwLambda := qwLambda
          psi := psi
          convolutionStar := convolutionStar
          globalPrimeIndexSet := globalPrimeIndexSet
          restrictedPrimeIndexSet := restrictedPrimeIndexSet
          finitePrimeAtomVisible := finitePrimeAtomVisible
          finitePrimeTerm := finitePrimeTerm
          archimedeanTerm := archimedeanTerm
          poleFunctional := poleFunctional
          polePairing := polePairing
          primePowerPairing := primePowerPairing
          vonMangoldtWeight := vonMangoldtWeight }
        (convolutionStar f g)
  restricted_prime_index_coverage :
    ∀ f g : TestFunction,
      ∀ lambda : ℝ,
        1 < lambda →
          WeilFormSymbols.RestrictedPrimeIndexCoverageStatement
            { qw := qw
              qwLambda := qwLambda
              psi := psi
              convolutionStar := convolutionStar
              globalPrimeIndexSet := globalPrimeIndexSet
              restrictedPrimeIndexSet := restrictedPrimeIndexSet
              finitePrimeAtomVisible := finitePrimeAtomVisible
              finitePrimeTerm := finitePrimeTerm
              archimedeanTerm := archimedeanTerm
              poleFunctional := poleFunctional
              polePairing := polePairing
              primePowerPairing := primePowerPairing
              vonMangoldtWeight := vonMangoldtWeight }
            lambda (convolutionStar f g)
  finite_prime_term_normalization :
    ∀ f g : TestFunction,
      WeilFormSymbols.FinitePrimeTermNormalizationStatement
        { qw := qw
          qwLambda := qwLambda
          psi := psi
          convolutionStar := convolutionStar
          globalPrimeIndexSet := globalPrimeIndexSet
          restrictedPrimeIndexSet := restrictedPrimeIndexSet
          finitePrimeAtomVisible := finitePrimeAtomVisible
          finitePrimeTerm := finitePrimeTerm
          archimedeanTerm := archimedeanTerm
          poleFunctional := poleFunctional
          polePairing := polePairing
          primePowerPairing := primePowerPairing
          vonMangoldtWeight := vonMangoldtWeight }
        f g
  pole_normalization :
    ∀ f : TestFunction, polePairing f = poleFunctional (convolutionStar f f)

namespace CCM25SourceModel

def toWeilFormSymbols (M : CCM25SourceModel) : WeilFormSymbols where
  qw := M.qw
  qwLambda := M.qwLambda
  psi := M.psi
  convolutionStar := M.convolutionStar
  globalPrimeIndexSet := M.globalPrimeIndexSet
  restrictedPrimeIndexSet := M.restrictedPrimeIndexSet
  finitePrimeAtomVisible := M.finitePrimeAtomVisible
  finitePrimeTerm := M.finitePrimeTerm
  archimedeanTerm := M.archimedeanTerm
  poleFunctional := M.poleFunctional
  polePairing := M.polePairing
  primePowerPairing := M.primePowerPairing
  vonMangoldtWeight := M.vonMangoldtWeight

@[simp]
theorem toWeilFormSymbols_qw
    (M : CCM25SourceModel) (f g : TestFunction) :
    M.toWeilFormSymbols.qw f g = M.qw f g :=
  rfl

@[simp]
theorem toWeilFormSymbols_psi
    (M : CCM25SourceModel) (F : TestFunction) :
    M.toWeilFormSymbols.psi F = M.psi F :=
  rfl

@[simp]
theorem toWeilFormSymbols_convolutionStar
    (M : CCM25SourceModel) (f g : TestFunction) :
    M.toWeilFormSymbols.convolutionStar f g =
      M.convolutionStar f g :=
  rfl

end CCM25SourceModel

/--
The first non-toy CCM25 theorem-base field: the source model's `QW` law is
projected into the compact Weil-form theorem statement.
-/
theorem ccm25_source_qw_definition
    (M : CCM25SourceModel) :
    WeilFormSymbols.QWDefinitionStatement M.toWeilFormSymbols := by
  intro f g
  exact M.qw_eq_psi_convolution f g

theorem ccm25_source_psi_sign
    (M : CCM25SourceModel) :
    WeilFormSymbols.PsiSignStatement M.toWeilFormSymbols := by
  intro F
  exact M.psi_sign_formula F

theorem ccm25_source_qw_lambda_formula
    (M : CCM25SourceModel) :
    WeilFormSymbols.QWLambdaFormulaStatement M.toWeilFormSymbols := by
  intro lambda hlambda f
  exact M.qw_lambda_formula lambda hlambda f

theorem ccm25_source_finite_prime_normalization
    (M : CCM25SourceModel) :
    WeilFormSymbols.FinitePrimeNormalizationStatement M.toWeilFormSymbols := by
  intro f g
  exact
    { globalPrimeIndexCoverage :=
        M.global_prime_index_coverage f g
      restrictedPrimeIndexCoverage :=
        M.restricted_prime_index_coverage f g
      finitePrimeTermNormalization :=
        M.finite_prime_term_normalization f g }

theorem ccm25_source_pole_normalization
    (M : CCM25SourceModel) :
    WeilFormSymbols.PoleNormalizationStatement M.toWeilFormSymbols := by
  intro f
  exact M.pole_normalization f

noncomputable def ccm25_source_model_of_arithmetic_rows
    {W : WeilFormSymbols}
    (rows : CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows W) :
    CCM25SourceModel where
  qw := W.qw
  convolutionStar := W.convolutionStar
  psi := W.psi
  qwLambda := W.qwLambda
  globalPrimeIndexSet := W.globalPrimeIndexSet
  restrictedPrimeIndexSet := W.restrictedPrimeIndexSet
  finitePrimeAtomVisible := W.finitePrimeAtomVisible
  finitePrimeTerm := W.finitePrimeTerm
  archimedeanTerm := W.archimedeanTerm
  poleFunctional := W.poleFunctional
  polePairing := W.polePairing
  primePowerPairing := W.primePowerPairing
  vonMangoldtWeight := W.vonMangoldtWeight
  qw_eq_psi_convolution :=
    CCM25Concrete.Rows.qw_definition_of_arithmetic_rows rows
  psi_sign_formula :=
    CCM25Concrete.Rows.psi_sign_of_arithmetic_rows rows
  qw_lambda_formula :=
    CCM25Concrete.Rows.qw_lambda_formula_of_arithmetic_rows rows
  global_prime_index_coverage := by
    intro f g
    exact
      (CCM25Concrete.Rows.finite_prime_normalization_of_arithmetic_rows
        rows f g).globalPrimeIndexCoverage
  restricted_prime_index_coverage := by
    intro f g lambda hlambda
    exact
      (CCM25Concrete.Rows.finite_prime_normalization_of_arithmetic_rows
        rows f g).restrictedPrimeIndexCoverage lambda hlambda
  finite_prime_term_normalization := by
    intro f g
    exact
      (CCM25Concrete.Rows.finite_prime_normalization_of_arithmetic_rows
        rows f g).finitePrimeTermNormalization
  pole_normalization :=
    CCM25Concrete.Rows.pole_normalization_of_arithmetic_rows rows

@[simp]
theorem ccm25_source_model_of_arithmetic_rows_to_weil_form_symbols
    {W : WeilFormSymbols}
    (rows : CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows W) :
    (ccm25_source_model_of_arithmetic_rows rows).toWeilFormSymbols = W := by
  cases W
  rfl

theorem ccm25_source_model_of_arithmetic_rows_qw_definition
    {W : WeilFormSymbols}
    (rows : CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows W) :
    ccm25_source_qw_definition
      (ccm25_source_model_of_arithmetic_rows rows) =
      CCM25Concrete.Rows.qw_definition_of_arithmetic_rows rows := by
  rfl

theorem ccm25_source_model_of_arithmetic_rows_psi_sign
    {W : WeilFormSymbols}
    (rows : CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows W) :
    ccm25_source_psi_sign
      (ccm25_source_model_of_arithmetic_rows rows) =
      CCM25Concrete.Rows.psi_sign_of_arithmetic_rows rows := by
  rfl

theorem ccm25_source_model_of_arithmetic_rows_qw_lambda
    {W : WeilFormSymbols}
    (rows : CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows W) :
    ccm25_source_qw_lambda_formula
      (ccm25_source_model_of_arithmetic_rows rows) =
      CCM25Concrete.Rows.qw_lambda_formula_of_arithmetic_rows rows := by
  rfl

theorem ccm25_source_model_of_arithmetic_rows_finite_prime
    {W : WeilFormSymbols}
    (rows : CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows W) :
    ccm25_source_finite_prime_normalization
      (ccm25_source_model_of_arithmetic_rows rows) =
      CCM25Concrete.Rows.finite_prime_normalization_of_arithmetic_rows rows := by
  funext f g
  rfl

theorem ccm25_source_model_of_arithmetic_rows_pole
    {W : WeilFormSymbols}
    (rows : CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows W) :
    ccm25_source_pole_normalization
      (ccm25_source_model_of_arithmetic_rows rows) =
      CCM25Concrete.Rows.pole_normalization_of_arithmetic_rows rows := by
  rfl

end Source
end ConnesWeilRH
