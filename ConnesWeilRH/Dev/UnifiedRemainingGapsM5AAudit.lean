/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete

/-!
# Plan 016 M5A import audit

This audit fixes the public signatures and axiom boundary of fixed-window
Mellin interpolation, the positive-to-log-coordinate bridge, and finite-prime
term vanishing.
-/

namespace ConnesWeilRH
namespace Dev
namespace UnifiedRemainingGapsM5AAudit

open Source
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
open CCM25Concrete.SelectedYoshidaBridge

#check weighted_mellin_kernel_log_window_independence
#check fixed_window_node_value_image_mellin_surjective
#check exists_fixedWindowYoshidaTest
#check convolutionSquare_support_subset_difference
#check selectedSquareOfWindow_finitePrimeTerm_eq_zero
#check fixedWindowSelectedSquare_finitePrimeTerm_eq_zero
#check fixedWindowSelectedFormula

#print fixed_window_node_value_image_mellin_surjective
#print exists_fixedWindowYoshidaTest

#print axioms weighted_mellin_kernel_log_window_independence
#print axioms fixed_window_node_value_image_mellin_surjective
#print axioms exists_fixedWindowYoshidaTest
#print axioms convolutionSquare_support_subset_difference
#print axioms selectedSquareOfWindow_finitePrimeTerm_eq_zero
#print axioms fixedWindowSelectedSquare_finitePrimeTerm_eq_zero
#print axioms fixedWindowSelectedFormula

end UnifiedRemainingGapsM5AAudit
end Dev
end ConnesWeilRH
