/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20YoshidaNearZeros
import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Source.CC20Concrete.RegularKernelCompactOperator
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The fixed Haar interval does not carry the global Mellin evaluations

The regular-kernel operator is defined on the compact interval `[1/2, 2]`,
whereas the route's Mellin evaluations are taken on the full positive line.
This file records the smallest formal obstruction to identifying those two
interfaces: a compact test supported in `(3, 4)` has zero restriction to the
Haar interval but can have a prescribed nonzero Mellin value.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open Filter
open scoped Topology
open CC20YoshidaNearZeros
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode

abbrev CC20CompactIntervalPoint := {x : ℝ // x ∈ CC20CompactInterval}

noncomputable def cc20CompactRestriction
    (g : normalizedCC20TestSpace.Test) :
      CC20CompactIntervalPoint → ℂ :=
  fun x => normalizedCC20ConcreteTestAlgebra.legacy.encode g x.1

theorem exists_test_zero_on_cc20CompactInterval_nonzero_global_mellin_one :
    ∃ g : normalizedCC20TestSpace.Test,
      (∀ x : CC20CompactIntervalPoint, cc20CompactRestriction g x = 0) ∧
        normalizedCC20TestSpace.mellinAt g 1 ≠ 0 := by
  obtain ⟨p, hsupp, hnonneg, him, hvalue⟩ :=
    exists_positive_interval_compact_test_real_bump
      (a := (3 : ℝ)) (b := (4 : ℝ)) (t := (7 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  let g := p.test
  have hzero : ∀ x : CC20CompactIntervalPoint,
      cc20CompactRestriction g x = 0 := by
    intro x
    by_contra hx
    have hmem : x.1 ∈ Function.support
        (fun t : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g t) := by
      simpa [Function.mem_support, cc20CompactRestriction] using hx
    have hwindow := hsupp hmem
    have hxupper : x.1 ≤ 2 := x.2.2
    linarith [hwindow.1]
  have hcomplex_integrable : Integrable
      (fun x : ℝ =>
        normalizedCC20ConcreteTestAlgebra.legacy.encode g x)
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul,
      IntegrableOn] using
      (testFunction_mellinConvergent_of_support_subset_Icc
        (normalizedCC20ConcreteTestAlgebra.legacy.encode g)
        (1 : ℂ) p.lower_pos p.support_subset)
  have hreal_integrable : Integrable
      (fun x : ℝ =>
        (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re)
      (volume.restrict (Set.Ioi 0)) := hcomplex_integrable.re
  have hreal_nonneg : ∀ x : ℝ,
      0 ≤ (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re :=
    hnonneg
  have hreal_at : 0 <
      (normalizedCC20ConcreteTestAlgebra.legacy.encode g (7 / 2 : ℝ)).re := by
    have hvalue_re := congrArg Complex.re hvalue
    rw [hvalue_re]
    norm_num
  have hcont : ContinuousAt
      (fun x : ℝ =>
        (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re)
      (7 / 2 : ℝ) :=
    Complex.continuous_re.continuousAt.comp
      (SchwartzMap.continuous
        (normalizedCC20ConcreteTestAlgebra.legacy.encode g)).continuousAt
  have hsupport_pos :
      0 < (volume.restrict (Set.Ioi 0))
        (Function.support (fun x : ℝ =>
          (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re)) := by
    have hevent : ∀ᶠ x in 𝓝 (7 / 2 : ℝ),
        0 < (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re :=
      hcont.eventually (isOpen_Ioi.mem_nhds hreal_at)
    rcases Filter.Eventually.exists_Ioo_subset hevent with
      ⟨lower, upper, htIoo, hIoo⟩
    let positiveLower : ℝ := max lower (7 / 4 : ℝ)
    have hlower_pos : 0 < positiveLower :=
      lt_max_of_lt_right (by norm_num)
    have hlower_lt_t : positiveLower < (7 / 2 : ℝ) :=
      max_lt htIoo.1 (by norm_num)
    have hlower_lt_upper : positiveLower < upper :=
      lt_trans hlower_lt_t htIoo.2
    have hsubset : Set.Ioo positiveLower upper ⊆
        Function.support (fun x : ℝ =>
          (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re) := by
      intro x hx
      rw [Function.mem_support]
      exact ne_of_gt (hIoo
        ⟨lt_of_le_of_lt (le_max_left lower (7 / 4)) hx.1, hx.2⟩)
    have hinterval_pos :
        0 < (volume.restrict (Set.Ioi 0))
          (Set.Ioo positiveLower upper) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      have hinter : Set.Ioo positiveLower upper ∩ Set.Ioi 0 =
          Set.Ioo positiveLower upper := by
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, lt_trans hlower_pos hx.1⟩
      rw [hinter, Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlower_lt_upper)
    exact measure_pos_of_superset hsubset hinterval_pos.ne'
  have hreal_pos : 0 < ∫ x : ℝ in Set.Ioi 0,
      (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re :=
    (integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall hreal_nonneg) hreal_integrable).2
      hsupport_pos
  have hmellin_ne : normalizedCC20TestSpace.mellinAt g 1 ≠ 0 := by
    intro hmellin_zero
    have hcomplex_zero :
        (∫ x : ℝ in Set.Ioi 0,
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) = 0 := by
      simpa [normalizedCC20TestSpace_mellinAt_eq,
        normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin, mellin] using
        hmellin_zero
    have hreal_zero :
        (∫ x : ℝ in Set.Ioi 0,
          (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re) = 0 := by
      calc
        (∫ x : ℝ in Set.Ioi 0,
            (normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re) =
            (∫ x : ℝ in Set.Ioi 0,
              normalizedCC20ConcreteTestAlgebra.legacy.encode g x).re :=
          (by
            simpa only [Complex.reCLM_apply] using
              (Complex.reCLM.integral_comp_comm hcomplex_integrable))
        _ = 0 := by rw [hcomplex_zero]; rfl
    linarith
  exact ⟨g, hzero, hmellin_ne⟩

theorem not_global_mellin_one_factors_through_cc20CompactRestriction :
    ¬ ∃ L : (CC20CompactIntervalPoint → ℂ) →ₗ[ℂ] ℂ,
      ∀ g : normalizedCC20TestSpace.Test,
        normalizedCC20TestSpace.mellinAt g 1 =
          L (cc20CompactRestriction g) := by
  rintro ⟨L, hL⟩
  obtain ⟨g, hzero, hmellin⟩ :=
    exists_test_zero_on_cc20CompactInterval_nonzero_global_mellin_one
  have hrestriction : cc20CompactRestriction g =
      (0 : CC20CompactIntervalPoint → ℂ) := by
    funext x
    exact hzero x
  have hfactor := hL g
  rw [hrestriction, map_zero] at hfactor
  exact hmellin hfactor

end CC20Concrete
end Source
end ConnesWeilRH
