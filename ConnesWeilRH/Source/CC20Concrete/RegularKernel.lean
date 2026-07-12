/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelCandidate
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Two-variable ordinary CC20 regular-kernel candidate

The Dirac mass on the diagonal is not part of this ordinary function.  This
module only lifts the proved non-diagonal scalar `Q(delta)` profile to positive
multiplicative coordinates.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open Filter
open MeasureTheory
open scoped Topology

/-- Positive real coordinate used by the multiplicative CC20 kernel. -/
abbrev PositiveCoordinate := {x : ℝ // 0 < x}

noncomputable def cc20SqrtILower : PositiveCoordinate :=
  ⟨(1 / 2 : ℝ), by norm_num⟩

noncomputable def cc20SqrtIUpper : PositiveCoordinate :=
  ⟨(2 : ℝ), by norm_num⟩

/-- A concrete compact `sqrt(I)` interval, with `I = [1/4, 4]`. -/
noncomputable def cc20SqrtI : Set PositiveCoordinate :=
  Set.Icc cc20SqrtILower cc20SqrtIUpper

noncomputable def cc20SqrtIRectangle :
    Set (PositiveCoordinate × PositiveCoordinate) :=
  cc20SqrtI ×ˢ cc20SqrtI

noncomputable def cc20SqrtIMap (x : ℝ) : PositiveCoordinate :=
  ⟨max x (1 / 2), by positivity⟩

/-- Symmetric multiplicative distance from the diagonal. -/
noncomputable def ratioRadius
    (p : PositiveCoordinate × PositiveCoordinate) : ℝ :=
  max ((p.1 : ℝ) / (p.2 : ℝ)) ((p.2 : ℝ) / (p.1 : ℝ))

/-- Ordinary two-variable part of the proposed CC20 compact remainder. -/
noncomputable def cc20QDeltaDiagonalValue : ℝ :=
  8 * Real.pi ^ 2 / 9 + sineIntegralQuotient (4 * Real.pi) - 1 / 2

/-- Measurable diagonal extension candidate for the ordinary `Q(delta)`
profile.  Continuity at `rho = 1` is a separate theorem. -/
noncomputable def cc20QDeltaRegularExtension (rho : ℝ) : ℝ :=
  if rho = 1 then cc20QDeltaDiagonalValue else cc20QDeltaRegularCandidate rho

/-- Ordinary two-variable part of the proposed CC20 compact remainder. -/
noncomputable def cc20RegularKernel
    (p : PositiveCoordinate × PositiveCoordinate) : ℝ :=
  cc20QDeltaRegularExtension (ratioRadius p)

@[simp]
theorem cc20QDeltaRegularExtension_one :
    cc20QDeltaRegularExtension 1 = cc20QDeltaDiagonalValue := by
  simp [cc20QDeltaRegularExtension]

theorem cc20QDeltaRegularExtension_of_ne_one {rho : ℝ} (hrho : rho ≠ 1) :
    cc20QDeltaRegularExtension rho = cc20QDeltaRegularCandidate rho := by
  simp [cc20QDeltaRegularExtension, hrho]

theorem continuousWithinAt_cc20QDeltaRegularExtension_Ici :
    ContinuousWithinAt cc20QDeltaRegularExtension (Set.Ici (1 : ℝ)) 1 := by
  let u : ℝ → ℝ := Function.update cc20QDeltaRegularContinuousCandidate 1
    cc20QDeltaDiagonalValue
  have hu : ContinuousAt u 1 := by
    apply continuousAt_update_same.mpr
    have h := continuousAt_cc20QDeltaRegularContinuousCandidate_one.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (1 : ℝ) ≤ 𝓝 1)
    simpa [u, cc20QDeltaRegularContinuousCandidate_one,
      cc20QDeltaDiagonalValue] using h
  have heq : ∀ rho ∈ Set.Ici (1 : ℝ),
      cc20QDeltaRegularExtension rho = u rho := by
    intro rho hrho
    by_cases h1 : rho = 1
    · subst rho
      simp [u, cc20QDeltaRegularExtension, cc20QDeltaRegularContinuousCandidate_one,
        cc20QDeltaDiagonalValue]
    · have hminus : rho ≠ -1 := by
        intro hm
        rw [hm] at hrho
        norm_num at hrho
      calc
        cc20QDeltaRegularExtension rho = cc20QDeltaRegularCandidate rho :=
          cc20QDeltaRegularExtension_of_ne_one h1
        _ = cc20QDeltaRegularContinuousCandidate rho :=
          (cc20QDeltaRegularContinuousCandidate_eq h1 hminus).symm
        _ = u rho := by simp [u, h1]
  apply hu.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with rho hrho
    exact heq rho hrho
  · exact heq 1 (by norm_num)

theorem continuousOn_cc20QDeltaRegularExtension_Ici :
    ContinuousOn cc20QDeltaRegularExtension (Set.Ici (1 : ℝ)) := by
  intro rho hrho
  by_cases h1 : rho = 1
  · subst rho
    exact continuousWithinAt_cc20QDeltaRegularExtension_Ici
  · have hrho' : 1 < rho := lt_of_le_of_ne hrho (Ne.symm h1)
    have hc := continuousAt_cc20QDeltaRegularCandidate_of_one_lt hrho'
    have heq : cc20QDeltaRegularExtension =ᶠ[𝓝 rho]
        cc20QDeltaRegularCandidate := by
      filter_upwards [eventually_ne_nhds h1] with y hy
      exact cc20QDeltaRegularExtension_of_ne_one hy
    exact (hc.congr_of_eventuallyEq heq).continuousWithinAt

theorem one_le_ratioRadius
    (p : PositiveCoordinate × PositiveCoordinate) : 1 ≤ ratioRadius p := by
  rcases le_total (p.1 : ℝ) (p.2 : ℝ) with h | h
  · exact le_trans ((one_le_div p.1.property).2 h) (le_max_right _ _)
  · exact le_trans ((one_le_div p.2.property).2 h) (le_max_left _ _)

theorem ratioRadius_swap
    (p : PositiveCoordinate × PositiveCoordinate) :
    ratioRadius (p.2, p.1) = ratioRadius p := by
  simp [ratioRadius, max_comm]

theorem ratioRadius_eq_one_iff
    (p : PositiveCoordinate × PositiveCoordinate) :
    ratioRadius p = 1 ↔ p.1 = p.2 := by
  constructor
  · intro h
    have huv : (p.1 : ℝ) / (p.2 : ℝ) ≤ 1 := by
      calc
        (p.1 : ℝ) / (p.2 : ℝ) ≤ ratioRadius p := le_max_left _ _
        _ = 1 := h
    have hvu : (p.2 : ℝ) / (p.1 : ℝ) ≤ 1 := by
      calc
        (p.2 : ℝ) / (p.1 : ℝ) ≤ ratioRadius p := le_max_right _ _
        _ = 1 := h
    apply Subtype.ext
    exact le_antisymm ((div_le_one p.2.property).1 huv)
      ((div_le_one p.1.property).1 hvu)
  · intro h
    have hval : (p.1 : ℝ) = (p.2 : ℝ) := congrArg Subtype.val h
    simp [ratioRadius, hval, ne_of_gt p.2.property]

theorem continuous_ratioRadius : Continuous ratioRadius := by
  have hfirst : Continuous (fun p : PositiveCoordinate × PositiveCoordinate =>
      (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hsecond : Continuous (fun p : PositiveCoordinate × PositiveCoordinate =>
      (p.2 : ℝ)) := continuous_subtype_val.comp continuous_snd
  exact (hfirst.div hsecond (fun p => ne_of_gt p.2.property)).max
    (hsecond.div hfirst (fun p => ne_of_gt p.1.property))

theorem continuousAt_cc20RegularKernel
    (p : PositiveCoordinate × PositiveCoordinate) :
    ContinuousAt cc20RegularKernel p := by
  have hscalar : ContinuousWithinAt cc20QDeltaRegularExtension
      (Set.Ici (1 : ℝ)) (ratioRadius p) := by
    by_cases h1 : ratioRadius p = 1
    · simpa [h1] using continuousWithinAt_cc20QDeltaRegularExtension_Ici
    · have hgt : 1 < ratioRadius p :=
        lt_of_le_of_ne (one_le_ratioRadius p) (Ne.symm h1)
      have hc := continuousAt_cc20QDeltaRegularCandidate_of_one_lt hgt
      have heq : cc20QDeltaRegularExtension =ᶠ[𝓝 (ratioRadius p)]
          cc20QDeltaRegularCandidate := by
        filter_upwards [eventually_ne_nhds h1] with y hy
        exact cc20QDeltaRegularExtension_of_ne_one hy
      exact (hc.congr_of_eventuallyEq heq).continuousWithinAt
  have hratio : ContinuousAt ratioRadius p :=
    continuous_ratioRadius.continuousAt
  have hmaps : Set.MapsTo ratioRadius Set.univ (Set.Ici (1 : ℝ)) := by
    intro q hq
    exact one_le_ratioRadius q
  have hcomp := hscalar.comp (f := ratioRadius) (x := p)
    hratio.continuousWithinAt hmaps
  have hcomp' : ContinuousAt (cc20QDeltaRegularExtension ∘ ratioRadius) p := by
    simpa only [continuousWithinAt_univ] using hcomp
  simpa [cc20RegularKernel, Function.comp_def] using hcomp'

theorem continuous_cc20RegularKernel : Continuous cc20RegularKernel := by
  exact continuous_iff_continuousAt.mpr (fun p => continuousAt_cc20RegularKernel p)

theorem continuousOn_cc20RegularKernel_sqrtIRectangle :
    ContinuousOn cc20RegularKernel cc20SqrtIRectangle := by
  intro p hp
  have hscalar := continuousOn_cc20QDeltaRegularExtension_Ici
    (ratioRadius p) (one_le_ratioRadius p)
  have hratio : ContinuousAt ratioRadius p := continuous_ratioRadius.continuousAt
  have hmaps : Set.MapsTo ratioRadius cc20SqrtIRectangle (Set.Ici (1 : ℝ)) := by
    intro q hq
    exact one_le_ratioRadius q
  have hcomp := hscalar.comp hratio.continuousWithinAt hmaps
  simpa [cc20RegularKernel, Function.comp_def] using hcomp

noncomputable def cc20RegularKernelReal (p : ℝ × ℝ) : ℝ :=
  cc20RegularKernel (cc20SqrtIMap p.1, cc20SqrtIMap p.2)

noncomputable def cc20RealSqrtIRectangle : Set (ℝ × ℝ) :=
  Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2

theorem continuousOn_cc20RegularKernelReal_sqrtIRectangle :
    ContinuousOn cc20RegularKernelReal cc20RealSqrtIRectangle := by
  intro p hp
  have hmap : ContinuousAt
      (fun q : ℝ × ℝ => (cc20SqrtIMap q.1, cc20SqrtIMap q.2)) p := by
    unfold cc20SqrtIMap
    fun_prop
  have hmaps : Set.MapsTo
      (fun q : ℝ × ℝ => (cc20SqrtIMap q.1, cc20SqrtIMap q.2))
      cc20RealSqrtIRectangle cc20SqrtIRectangle := by
    intro q hq
    constructor
    · change cc20SqrtILower ≤ cc20SqrtIMap q.1 ∧
        cc20SqrtIMap q.1 ≤ cc20SqrtIUpper
      change (1 / 2 : ℝ) ≤ max q.1 (1 / 2) ∧ max q.1 (1 / 2) ≤ 2
      constructor
      · exact le_max_right _ _
      · rw [max_eq_left hq.1.1]
        exact hq.1.2
    · change cc20SqrtILower ≤ cc20SqrtIMap q.2 ∧
        cc20SqrtIMap q.2 ≤ cc20SqrtIUpper
      change (1 / 2 : ℝ) ≤ max q.2 (1 / 2) ∧ max q.2 (1 / 2) ≤ 2
      constructor
      · exact le_max_right _ _
      · rw [max_eq_left hq.2.1]
        exact hq.2.2
  have hcomp := continuousOn_cc20RegularKernel_sqrtIRectangle
    (cc20SqrtIMap p.1, cc20SqrtIMap p.2) (hmaps hp)
  have hresult := hcomp.comp
    (f := fun q : ℝ × ℝ => (cc20SqrtIMap q.1, cc20SqrtIMap q.2))
    (x := p) hmap.continuousWithinAt hmaps
  simpa [cc20RegularKernelReal, Function.comp_def] using hresult

theorem integrableOn_cc20RegularKernelReal_sq_sqrtIRectangle :
    IntegrableOn (fun p : ℝ × ℝ => ‖cc20RegularKernelReal p‖ ^ 2)
      cc20RealSqrtIRectangle := by
  have hcompact : IsCompact cc20RealSqrtIRectangle := by
    unfold cc20RealSqrtIRectangle
    exact isCompact_Icc.prod isCompact_Icc
  apply ContinuousOn.integrableOn_compact hcompact
  exact continuousOn_cc20RegularKernelReal_sqrtIRectangle.norm.pow 2

theorem measurable_cc20QDeltaRegularCandidate :
    Measurable cc20QDeltaRegularCandidate := by
  unfold cc20QDeltaRegularCandidate cc20DeltaRegularDerivative
    cc20DeltaRegularSecondDerivative cc20DeltaRegular
    siQuotientProfile siQuotientDerivativeProfile
    sineIntegralQuotientSecondDerivativeProfile
  fun_prop

theorem measurable_cc20RegularKernel : Measurable cc20RegularKernel := by
  have hextension : Measurable cc20QDeltaRegularExtension := by
    unfold cc20QDeltaRegularExtension
    exact Measurable.ite (measurableSet_singleton 1) measurable_const
      measurable_cc20QDeltaRegularCandidate
  exact hextension.comp continuous_ratioRadius.measurable

theorem cc20RegularKernel_diagonal (u : PositiveCoordinate) :
    cc20RegularKernel (u, u) = cc20QDeltaDiagonalValue := by
  simp [cc20RegularKernel, ratioRadius, ne_of_gt u.property]

theorem continuousAt_cc20RegularKernel_diagonal (u : PositiveCoordinate) :
    ContinuousAt cc20RegularKernel (u, u) := by
  have hscalar := continuousWithinAt_cc20QDeltaRegularExtension_Ici
  have hratio : ContinuousAt ratioRadius (u, u) :=
    continuous_ratioRadius.continuousAt
  have hmaps : Set.MapsTo ratioRadius Set.univ (Set.Ici (1 : ℝ)) := by
    intro p hp
    exact one_le_ratioRadius p
  have hdiag : ratioRadius (u, u) = 1 := by
    simp [ratioRadius, ne_of_gt u.property]
  have hscalar' : ContinuousWithinAt cc20QDeltaRegularExtension
      (Set.Ici (1 : ℝ)) (ratioRadius (u, u)) := by
    simpa [hdiag] using hscalar
  have hcomp := hscalar'.comp (f := ratioRadius) (x := (u, u))
    hratio.continuousWithinAt hmaps
  rw [← continuousWithinAt_univ]
  simpa [cc20RegularKernel, ratioRadius, Function.comp_def, ne_of_gt u.property] using hcomp

theorem cc20RegularKernel_off_diagonal
    (p : PositiveCoordinate × PositiveCoordinate) (hp : p.1 ≠ p.2) :
    cc20RegularKernel p = cc20QDeltaRegularCandidate (ratioRadius p) := by
  apply cc20QDeltaRegularExtension_of_ne_one
  exact (ratioRadius_eq_one_iff p).not.mpr hp

theorem cc20RegularKernel_swap
    (p : PositiveCoordinate × PositiveCoordinate) :
    cc20RegularKernel (p.2, p.1) = cc20RegularKernel p := by
  simp [cc20RegularKernel, ratioRadius_swap]

end CC20Concrete
end Source
end ConnesWeilRH
