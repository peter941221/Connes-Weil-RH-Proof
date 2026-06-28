/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25

/-!
# CCM25 restricted QW_lambda/pole spine

This small module exposes only the restricted-form and pole-normalization rows.
It deliberately does not claim restricted-to-full equality.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace Restricted

theorem qw_lambda_formula_statement
    (ccm25 : CCM25Interface) :
    WeilFormSymbols.QWLambdaFormulaStatement ccm25.weilSymbols :=
  ccm25.qwLambdaFormula

theorem pole_normalization_statement
    (ccm25 : CCM25Interface) :
    WeilFormSymbols.PoleNormalizationStatement ccm25.weilSymbols :=
  ccm25.poleNormalization

end Restricted
end CCM25Concrete
end Source
end ConnesWeilRH
