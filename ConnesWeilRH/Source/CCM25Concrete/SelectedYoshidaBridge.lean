/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Source.CCM25Concrete.SelectedArchimedeanIntegrability

/-!
# Fixed-window Yoshida tests in the CCM25 log coordinate

This module keeps one positive-variable Yoshida test tied to its pullback under
`Real.exp`.  The pullback is the additive log-coordinate test used by the
selected CCM25 convolution square.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace SelectedYoshidaBridge

open MeasureTheory
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
open CompactLogConvolution
open scoped ContDiff

noncomputable def logPullbackRaw
    (g : normalizedCC20ConcreteTestAlgebra.Test) (u : ℝ) : ℂ :=
  normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp u)

theorem logPullbackRaw_contDiff
    (g : normalizedCC20ConcreteTestAlgebra.Test) :
    ContDiff ℝ ∞ (logPullbackRaw g) := by
  exact
    ((normalizedCC20ConcreteTestAlgebra.legacy.encode g).smooth ⊤).comp
      Real.contDiff_exp

theorem logPullbackRaw_support_subset
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b) :
    Function.support (logPullbackRaw g) ⊆
      Set.Ioo (Real.log a) (Real.log b) := by
  intro u hu
  have hexp_mem :
      Real.exp u ∈ Function.support
        (fun t : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g t) := by
    simpa [logPullbackRaw] using hu
  have hwindow := hsupp hexp_mem
  constructor
  · exact (Real.log_lt_iff_lt_exp ha).mpr hwindow.1
  · exact (Real.lt_log_iff_exp_lt hb).mpr hwindow.2

noncomputable def compactLogTestOfWindow
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b) : CompactLogTest := by
  have hsupportIoo :
      Function.support (logPullbackRaw g) ⊆
        Set.Ioo (Real.log a) (Real.log b) :=
    logPullbackRaw_support_subset g ha hb hsupp
  have hcompact : HasCompactSupport (logPullbackRaw g) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (hsupportIoo.trans Set.Ioo_subset_Icc_self)
  exact
    { test := hcompact.toSchwartzMap (logPullbackRaw_contDiff g)
      compactSupport := by simpa using hcompact }

@[simp] theorem compactLogTestOfWindow_apply
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b)
    (u : ℝ) :
    (compactLogTestOfWindow g ha hb hsupp).test u =
      normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp u) :=
  rfl

theorem compactLogTestOfWindow_support_subset
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b) :
    Function.support (compactLogTestOfWindow g ha hb hsupp).test ⊆
      Set.Ioo (Real.log a) (Real.log b) := by
  simpa only [compactLogTestOfWindow_apply] using
    logPullbackRaw_support_subset g ha hb hsupp

theorem convolutionSquare_support_subset_difference
    (g : CompactLogTest) {lower upper : ℝ}
    (hsupp : Function.support g.test ⊆ Set.Ioo lower upper) :
    Function.support g.convolutionSquare.test ⊆
      Set.Ioo (lower - upper) (upper - lower) := by
  intro x hx
  have hxconv :
      x ∈ Function.support
        (MeasureTheory.convolution g.involution.test g.test
          (ContinuousLinearMap.mul ℝ ℂ) volume) := by
    simpa [CompactLogTest.convolutionSquare_apply] using hx
  have hxadd :=
    MeasureTheory.support_convolution_subset
      (ContinuousLinearMap.mul ℝ ℂ) hxconv
  rcases Set.mem_add.mp hxadd with ⟨y, hy, z, hz, hyz⟩
  have hy_source : -y ∈ Function.support g.test := by
    rw [Function.mem_support] at hy ⊢
    intro hzero
    apply hy
    simp [CompactLogTest.involution_apply, hzero]
  have hy_bounds := hsupp hy_source
  have hz_bounds := hsupp hz
  rcases hy_bounds with ⟨hy_lower, hy_upper⟩
  rcases hz_bounds with ⟨hz_lower, hz_upper⟩
  constructor <;> linarith

theorem compactLogTestOfWindow_convolutionSquare_support_subset
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b) :
    Function.support
        (compactLogTestOfWindow g ha hb hsupp).convolutionSquare.test ⊆
      Set.Ioo (Real.log a - Real.log b) (Real.log b - Real.log a) :=
  convolutionSquare_support_subset_difference
    (g := compactLogTestOfWindow g ha hb hsupp)
    (compactLogTestOfWindow_support_subset g ha hb hsupp)

noncomputable def selectedSquareOfWindow
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b) :
    SelectedWeilSquare.SelectedWeilSquareOwner where
  sourceTest := compactLogTestOfWindow g ha hb hsupp
  supportRadius := Real.log b - Real.log a
  supportRadius_nonnegative := by
    exact sub_nonneg.mpr (Real.log_le_log ha hab.le)
  convolutionSquare_support := by
    intro x hx
    have hbounds :=
      compactLogTestOfWindow_convolutionSquare_support_subset
        g ha hb hsupp hx
    rcases hbounds with ⟨hlower, hupper⟩
    constructor <;> linarith

@[simp] theorem selectedSquareOfWindow_sourceTest
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b) :
    (selectedSquareOfWindow g ha hb hab hsupp).sourceTest =
      compactLogTestOfWindow g ha hb hsupp :=
  rfl

theorem selectedSquareOfWindow_convolutionSquare_support_strict
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b) :
    Function.support
        (selectedSquareOfWindow g ha hb hab hsupp).convolutionSquare.test ⊆
      Set.Ioo (Real.log a - Real.log b) (Real.log b - Real.log a) := by
  simpa [SelectedWeilSquare.SelectedWeilSquareOwner.convolutionSquare] using
    compactLogTestOfWindow_convolutionSquare_support_subset g ha hb hsupp

theorem selectedSquareOfWindow_finitePrimeTerm_eq_zero
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo a b)
    (hwidth : Real.log b - Real.log a < Real.log 2)
    {n : ℕ} (hn : 2 ≤ n) :
    (selectedSquareOfWindow g ha hb hab hsupp).finitePrimeTerm n = 0 := by
  let owner := selectedSquareOfWindow g ha hb hab hsupp
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have htwo_n : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hlog_two_n : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) htwo_n
  have hradius_log_n :
      Real.log b - Real.log a < Real.log n :=
    hwidth.trans_le hlog_two_n
  have hsupport :=
    selectedSquareOfWindow_convolutionSquare_support_strict
      g ha hb hab hsupp
  have hplus : owner.convolutionSquare.test (Real.log n) = 0 := by
    by_contra hne
    have hbounds := hsupport hne
    rcases hbounds with ⟨_hlower, hupper⟩
    linarith
  have hminus : owner.convolutionSquare.test (-Real.log n) = 0 := by
    by_contra hne
    have hbounds := hsupport hne
    rcases hbounds with ⟨hlower, _hupper⟩
    linarith
  simp [owner, SelectedWeilSquare.SelectedWeilSquareOwner.finitePrimeTerm,
    SelectedWeilSquare.SelectedWeilSquareOwner.primePowerValue, hplus, hminus]

noncomputable def fixedWindowLower : ℝ := 3 / 4

noncomputable def fixedWindowUpper : ℝ := 5 / 4

theorem fixedWindowLower_pos : 0 < fixedWindowLower := by
  norm_num [fixedWindowLower]

theorem fixedWindowLower_lt_one : fixedWindowLower < 1 := by
  norm_num [fixedWindowLower]

theorem one_lt_fixedWindowUpper : 1 < fixedWindowUpper := by
  norm_num [fixedWindowUpper]

theorem fixedWindowUpper_pos : 0 < fixedWindowUpper :=
  lt_trans zero_lt_one one_lt_fixedWindowUpper

theorem fixedWindowLower_lt_upper : fixedWindowLower < fixedWindowUpper :=
  fixedWindowLower_lt_one.trans one_lt_fixedWindowUpper

theorem fixedWindow_logWidth_lt_log_two :
    Real.log fixedWindowUpper - Real.log fixedWindowLower < Real.log 2 := by
  rw [← Real.log_div (ne_of_gt fixedWindowUpper_pos)
    (ne_of_gt fixedWindowLower_pos)]
  apply Real.log_lt_log
  · norm_num [fixedWindowLower, fixedWindowUpper]
  · norm_num [fixedWindowLower, fixedWindowUpper]

theorem exists_fixedWindowYoshidaTest
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo fixedWindowLower fixedWindowUpper ∧
      ConcreteExpandedMellinRealizes rho g := by
  rcases fixed_window_node_value_image_mellin_surjective
      (rho := rho) fixedWindowLower_pos fixedWindowLower_lt_one
      one_lt_fixedWindowUpper
      (fun z => targetValueOnNodeValue rho z.1) with
    ⟨g, hcompact, hsupp, hvalue⟩
  refine ⟨g, hcompact, hsupp, ?_⟩
  intro i
  have hvalue_i :
      normalizedCC20TestSpace.mellinAt g (nodeValue rho i) =
        targetValueOnNodeValue rho (nodeValue rho i) := by
    simpa using
      hvalue ⟨nodeValue rho i, by simp [expandedNodeValueFinset]⟩
  rw [hvalue_i]
  exact targetValueOnNodeValue_eq_targetValue hrho hoff i

noncomputable def fixedWindowSelectedSquare
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo fixedWindowLower fixedWindowUpper) :
    SelectedWeilSquare.SelectedWeilSquareOwner :=
  selectedSquareOfWindow g fixedWindowLower_pos fixedWindowUpper_pos
    fixedWindowLower_lt_upper hsupp

theorem fixedWindowSelectedSquare_finitePrimeTerm_eq_zero
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo fixedWindowLower fixedWindowUpper)
    {n : ℕ} (hn : 2 ≤ n) :
    (fixedWindowSelectedSquare g hsupp).finitePrimeTerm n = 0 := by
  exact selectedSquareOfWindow_finitePrimeTerm_eq_zero
    g fixedWindowLower_pos fixedWindowUpper_pos fixedWindowLower_lt_upper
    hsupp fixedWindow_logWidth_lt_log_two hn

noncomputable def fixedWindowSelectedFormula
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupp :
      Function.support
          (fun t : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g t) ⊆
        Set.Ioo fixedWindowLower fixedWindowUpper) :
    SelectedWeilFormula.SelectedWeilFormulaOwner :=
  SelectedWeilFormula.SelectedWeilFormulaOwner.ofSquare
    (fixedWindowSelectedSquare g hsupp)

end SelectedYoshidaBridge
end CCM25Concrete
end Source
end ConnesWeilRH
