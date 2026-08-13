import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.MellinConvolutionIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# C1LogPositiveBridge - compact-log tests as positive-variable route tests

`CompactLogTest.test` is a function of the additive coordinate `u = log x`.
The route-facing `TestFunction` is instead a function of the positive variable
`x`.  These functions have the same Lean type, but they are not the same
mathematical object.

This module implements the missing inverse coordinate map

    route(F)(x) = F(log x),  x > 0,
                  0,         x <= 0.

Compact support of `F` makes this extension identically zero near `x = 0`, so
it is smooth and compactly supported on all of `Real`.  The final theorem
proves that its positive-variable Mellin transform is exactly the bilateral
Laplace transform of the original log test.
-/

namespace ConnesWeilRH
namespace Source
namespace C1LogPositiveBridge

open MeasureTheory
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open Dev.MellinConvolutionIdentity

/-- Extend a compact log-coordinate test to the positive multiplicative line. -/
noncomputable def positiveRouteRaw (F : CompactLogTest) (x : Real) : Complex :=
  if 0 < x then F.test (Real.log x) else 0

theorem positiveRouteRaw_eq_zero_of_lt_exp_neg_supportRadius
    (F : CompactLogTest) {x : Real}
    (hx : x < Real.exp (-supportRadius F)) :
    positiveRouteRaw F x = 0 := by
  by_cases hxpos : 0 < x
  · have hlog : Real.log x < -supportRadius F :=
      (Real.log_lt_iff_lt_exp hxpos).2 hx
    have hvalue : F.test (Real.log x) = 0 := by
      by_contra hne
      exact (not_lt_of_ge (support_subset_Icc F hne).1) hlog
    simp [positiveRouteRaw, hxpos, hvalue]
  · simp [positiveRouteRaw, hxpos]

/-- The zero extension is smooth at every real point.  At positive points this
is smooth composition with `log`; at nonpositive points it is locally zero. -/
theorem positiveRouteRaw_contDiff (F : CompactLogTest) :
    ContDiff Real (⊤ : ℕ∞) (positiveRouteRaw F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hxpos : 0 < x
  · have hcomp :
        ContDiffAt Real (⊤ : ℕ∞) (fun y : Real => F.test (Real.log y)) x :=
      (F.test.smooth ⊤).contDiffAt.comp x (Real.contDiffAt_log.2 hxpos.ne')
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    have hypos : 0 < y := hy
    rw [positiveRouteRaw, if_pos hypos]
  · have hxlt : x < Real.exp (-supportRadius F) :=
      (le_of_not_gt hxpos).trans_lt (Real.exp_pos _)
    have hzero :
        ContDiffAt Real (⊤ : ℕ∞) (fun _ : Real => (0 : Complex)) x :=
      contDiffAt_const
    apply hzero.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxlt] with y hy
    exact positiveRouteRaw_eq_zero_of_lt_exp_neg_supportRadius F hy

theorem positiveRouteRaw_support_subset (F : CompactLogTest) :
    Function.support (positiveRouteRaw F) ⊆
      Set.Icc (Real.exp (-supportRadius F)) (Real.exp (supportRadius F)) := by
  intro x hx
  have hxpos : 0 < x := by
    by_contra hnot
    apply hx
    simp [positiveRouteRaw, hnot]
  have hlogValue : F.test (Real.log x) ≠ 0 := by
    simpa [positiveRouteRaw, hxpos] using hx
  have hlogBounds := support_subset_Icc F hlogValue
  constructor
  · rw [← Real.exp_log hxpos]
    exact Real.exp_le_exp.mpr hlogBounds.1
  · rw [← Real.exp_log hxpos]
    exact Real.exp_le_exp.mpr hlogBounds.2

theorem positiveRouteRaw_compactSupport (F : CompactLogTest) :
    HasCompactSupport (positiveRouteRaw F) := by
  apply HasCompactSupport.intro
    (K := Set.Icc (Real.exp (-supportRadius F)) (Real.exp (supportRadius F)))
    isCompact_Icc
  intro x hx
  by_contra hne
  exact hx (positiveRouteRaw_support_subset F hne)

/-- The genuine positive-variable Schwartz test attached to a compact log test. -/
noncomputable def toPositiveRouteTest (F : CompactLogTest) : TestFunction :=
  (positiveRouteRaw_compactSupport F).toSchwartzMap (positiveRouteRaw_contDiff F)

@[simp] theorem toPositiveRouteTest_apply (F : CompactLogTest) (x : Real) :
    toPositiveRouteTest F x =
      if 0 < x then F.test (Real.log x) else 0 := by
  rfl

/-- Pulling the route test back by `exp` recovers the original log test. -/
@[simp] theorem toPositiveRouteTest_exp (F : CompactLogTest) (u : Real) :
    toPositiveRouteTest F (Real.exp u) = F.test u := by
  simp [toPositiveRouteTest_apply, Real.exp_pos, Real.log_exp]

theorem toPositiveRouteTest_compactSupport (F : CompactLogTest) :
    HasCompactSupport (toPositiveRouteTest F) := by
  simpa only [toPositiveRouteTest_apply] using positiveRouteRaw_compactSupport F

private theorem ofReal_exp_cpow (u : Real) (s : Complex) :
    (Real.exp u : Complex) ^ s = Complex.exp (s * (u : Complex)) := by
  rw [Complex.cpow_def_of_ne_zero (by simp)]
  rw [← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  congr 1
  ring

/-- The coordinate contract: positive-variable Mellin evaluation equals the
bilateral Laplace evaluation of the same compact log owner. -/
theorem mellin_toPositiveRouteTest_eq_laplaceAt
    (F : CompactLogTest) (s : Complex) :
    mellin (fun x : Real => toPositiveRouteTest F x) s =
      CompactLogTest.laplaceAt F s := by
  calc
    mellin (fun x : Real => toPositiveRouteTest F x) s =
        mellin (fun x : Real => F.test (Real.log x)) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxpos : 0 < x := hx
      change
        (x : Complex) ^ (s - 1) • toPositiveRouteTest F x =
          (x : Complex) ^ (s - 1) • F.test (Real.log x)
      rw [toPositiveRouteTest_apply, if_pos hxpos]
    _ = ∫ u : Real in Set.univ, (Real.exp u : Complex) ^ s • F.test u :=
      mellin_comp_log_eq_exp_integral (fun u : Real => F.test u) s
    _ = ∫ u : Real, Complex.exp (s * (u : Complex)) * F.test u := by
      rw [setIntegral_univ]
      apply integral_congr_ae
      filter_upwards with u
      rw [ofReal_exp_cpow]
      simp only [smul_eq_mul]
    _ = CompactLogTest.laplaceAt F s := by
      unfold CompactLogTest.laplaceAt
      simp only [CompactLogTest.exponentialWeight_apply]

end C1LogPositiveBridge
end Source
end ConnesWeilRH
