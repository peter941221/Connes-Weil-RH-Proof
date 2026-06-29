/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.ObjectDerivations

/-!
# CCM25 source interface

This file names the CCM25 inputs used to read the no-defect quantized trace as
the restricted and full Weil quadratic forms.
-/

namespace ConnesWeilRH
namespace Source

variable (W : WeilFormSymbols)

def ccm25QWDefinition : SourceObligation where
  sourceKey := "CCM25"
  sourceFile := "mc2arXiv.tex"
  lineRange := "445-470"
  manuscriptRole :=
    "QW(f,g)=Psi(f^* * g), finite-prime terms, archimedean sign, and pole functional"
  statement :=
    WeilFormSymbols.QWDefinitionStatement W ∧
      WeilFormSymbols.PsiSignStatement W

def ccm25QWLambdaFormula : SourceObligation where
  sourceKey := "CCM25"
  sourceFile := "mc2arXiv.tex"
  lineRange := "530-540"
  manuscriptRole :=
    "restricted QW_lambda formula and prime-power operator pairing"
  statement := WeilFormSymbols.QWLambdaFormulaStatement W

def ccm25FinitePrimeNormalization : SourceObligation where
  sourceKey := "CCM25"
  sourceFile := "mc2arXiv.tex"
  lineRange := "445-470, 530-540"
  manuscriptRole :=
    "finite-prime sign and von Mangoldt normalization in the restricted form"
  statement := WeilFormSymbols.FinitePrimeNormalizationStatement W

def ccm25PoleNormalization : SourceObligation where
  sourceKey := "CCM25"
  sourceFile := "mc2arXiv.tex"
  lineRange := "465-470, 533-535"
  manuscriptRole :=
    "pole functional W_(0,2) and restricted pole pairing"
  statement := WeilFormSymbols.PoleNormalizationStatement W

structure CCM25Interface where
  weilSymbols : WeilFormSymbols
  qwDefinition : (ccm25QWDefinition weilSymbols).Holds
  qwLambdaFormula : (ccm25QWLambdaFormula weilSymbols).Holds
  finitePrimeNormalization : (ccm25FinitePrimeNormalization weilSymbols).Holds
  poleNormalization : (ccm25PoleNormalization weilSymbols).Holds

namespace CCM25Interface

def ofSourceObjectPackage
    (pkg : SourceObject.SourceObjectPackage) : CCM25Interface where
  weilSymbols := pkg.toWeilFormSymbols
  qwDefinition :=
    ⟨SourceObject.SourceObjectPackage.provesQWDefinitionStatement pkg,
      SourceObject.SourceObjectPackage.provesPsiSignStatement pkg⟩
  qwLambdaFormula :=
    SourceObject.SourceObjectPackage.provesQWLambdaFormulaStatement pkg
  finitePrimeNormalization :=
    SourceObject.SourceObjectPackage.provesFinitePrimeNormalizationStatement pkg
  poleNormalization :=
    SourceObject.SourceObjectPackage.provesPoleNormalizationStatement pkg

theorem finite_prime_pointwise_term_of_source_object_package
    (pkg : SourceObject.SourceObjectPackage) :
    ∀ f g : TestFunction,
      WeilFormSymbols.FinitePrimeTermNormalizationStatement
        (ofSourceObjectPackage pkg).weilSymbols f g :=
  SourceObject.SourceObjectPackage.provesFinitePrimePointwiseTermStatement pkg

end CCM25Interface

end Source
end ConnesWeilRH
