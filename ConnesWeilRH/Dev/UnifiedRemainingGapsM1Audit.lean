/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete

/-!
# Plan 016 M1 import audit

This import-facing audit fixes the public declarations and axiom boundary of
the selected CCM25 formula owner.
-/

namespace ConnesWeilRH
namespace Dev
namespace UnifiedRemainingGapsM1Audit

open Source.CCM25Concrete

#check CompactLogConvolution.CompactLogTest.convolutionSquare_neg
#check SelectedWeilSquare.SelectedWeilSquareOwner.finitePrimeTerm_eq_real
#check SelectedWeilFormula.SelectedWeilFormulaOwner.ofSquare
#check SelectedWeilFormula.SelectedWeilFormulaOwner.restrictedWeilValue_eq_weilValue_add_omitted
#check SelectedWeilFormula.SelectedWeilFormulaOwner.weilValue_im_eq_zero

#print SelectedWeilFormula.SelectedWeilFormulaOwner.ofSquare

#print axioms CompactLogConvolution.CompactLogTest.convolutionSquare_neg
#print axioms SelectedWeilSquare.SelectedWeilSquareOwner.finitePrimeTerm_eq_real
#print axioms SelectedWeilFormula.SelectedWeilFormulaOwner.ofSquare
#print axioms SelectedWeilFormula.SelectedWeilFormulaOwner.restrictedWeilValue_eq_weilValue_add_omitted
#print axioms SelectedWeilFormula.SelectedWeilFormulaOwner.weilValue_im_eq_zero

end UnifiedRemainingGapsM1Audit
end Dev
end ConnesWeilRH
