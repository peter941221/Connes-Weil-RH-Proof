/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20YoshidaConstruction

/-!
# Finite multiplicative windows for positive compact tests

The regular-kernel model currently uses one fixed interval `[1/2,2]`.
CC20's finite-window route instead uses `[1/lambda,lambda]` with `lambda`
eventually large.  This file proves the elementary carrier inclusion needed
before defining a parameterized Haar operator: every positive compact test
window is contained in one such finite multiplicative window.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open CC20YoshidaInterpolationNode

abbrev cc20WindowInterval (lambda : ℝ) : Set ℝ :=
  Set.Icc (1 / lambda) lambda

theorem exists_cc20Window_containing_positiveIntervalCompactTest
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    ∃ lambda : ℝ,
      1 < lambda ∧
        Set.Icc p.lower p.upper ⊆ cc20WindowInterval lambda := by
  let bound : ℝ := max 1 (max p.upper (1 / p.lower))
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  let lambda : ℝ := n
  have hbound : bound < lambda := by
    simpa [lambda] using hn
  have hlambda_one : 1 < lambda := lt_of_le_of_lt (le_max_left _ _) hbound
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda_one
  have hlambda_upper : p.upper < lambda :=
    lt_of_le_of_lt
      (le_trans (le_max_left p.upper (1 / p.lower))
        (le_max_right 1 (max p.upper (1 / p.lower)))) hbound
  have hlambda_inv : 1 / lambda < p.lower := by
    have hrecip : 1 / lambda < 1 / (1 / p.lower) := by
      apply one_div_lt_one_div_of_lt
      · exact div_pos (by norm_num) p.lower_pos
      · exact lt_of_le_of_lt
          (le_trans (le_max_right p.upper (1 / p.lower))
            (le_max_right 1 (max p.upper (1 / p.lower)))) hbound
    simpa [one_div_div] using hrecip
  refine ⟨lambda, hlambda_one, ?_⟩
  intro x hx
  refine ⟨?_, ?_⟩
  · exact le_trans (le_of_lt hlambda_inv) hx.1
  · exact le_trans hx.2 (le_of_lt hlambda_upper)

theorem positiveIntervalCompactTest_support_subset_cc20Window
    (p : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    ∃ lambda : ℝ,
      1 < lambda ∧
        Function.support
            (fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ⊆
          cc20WindowInterval lambda := by
  obtain ⟨lambda, hlambda, hwindow⟩ :=
    exists_cc20Window_containing_positiveIntervalCompactTest p
  refine ⟨lambda, hlambda, ?_⟩
  exact p.support_subset.trans hwindow

end CC20Concrete
end Source
end ConnesWeilRH
