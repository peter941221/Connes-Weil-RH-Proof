/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25

/-!
# CCM25 global QW/Psi spine

This small module exposes only the global CCM25 rows:

* `QW(f,g)=Psi(f^* * g)`
* the visible `Psi` sign expansion.

It does not discuss `QW_lambda`, pole separation, finite-prime support, or the
restricted-to-full bridge.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace Global

theorem qw_definition_statement
    (ccm25 : CCM25Interface) :
    WeilFormSymbols.QWDefinitionStatement ccm25.weilSymbols :=
  ccm25.qwDefinition

theorem psi_sign_expansion_statement
    (ccm25 : CCM25Interface) :
    WeilFormSymbols.PsiSignStatement ccm25.weilSymbols :=
  ccm25.psiSign

end Global
end CCM25Concrete
end Source
end ConnesWeilRH
