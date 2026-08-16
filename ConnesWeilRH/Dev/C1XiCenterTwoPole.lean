import ConnesWeilRH.Dev.C1XiCenterTwoPrimePower
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# C1XiCenterTwoPole - full-line elementary-pole readback at `Re(s)=2`

The elementary factors `1 / s` and `1 / (s - 1)` are Laplace transforms of
decaying exponentials on the positive half-line.  Fubini and the existing
Fourier inversion theorem therefore read their center-`2` full-line integral
back to the two bilateral Laplace values in `C1SameOwnerWeil.poleTerm`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoPole

open MeasureTheory
open Complex
open Filter
open Set
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1XiArithmeticIntervalReadback
open C1XiArithmeticPrimePowerReadback
open C1XiCenterTwoPrimePower
open C1XiVerticalFunctional
open scoped Topology

noncomputable section

private theorem integrable_and_integral_mul_resolvent
    (phi psi : Real -> Complex)
    (hphi : Integrable phi)
    (hreadback : forall y : Real,
      (∫ t : Real,
        phi t * Complex.exp (-((t : Complex) * (y : Complex) * Complex.I))) =
          (2 * (Real.pi : Complex)) * psi y)
    {a : Real} (ha : 0 < a) :
    Integrable (fun t : Real =>
        phi t / ((a : Complex) + (t : Complex) * Complex.I)) /\
      (∫ t : Real,
        phi t / ((a : Complex) + (t : Complex) * Complex.I)) =
        (2 * (Real.pi : Complex)) *
          (∫ y : Real in Ioi 0,
            Complex.exp ((-(a : Real) : Complex) * (y : Complex)) * psi y) := by
  let h : Real -> Real -> Complex := fun t y =>
    (phi t * Complex.exp ((-(a : Real) : Complex) * (y : Complex))) *
      Complex.exp (-((t : Complex) * (y : Complex) * Complex.I))
  have hexp : Integrable
      (fun y : Real =>
        Complex.exp ((-(a : Real) : Complex) * (y : Complex)))
      (volume.restrict (Ioi 0)) := by
    exact integrableOn_exp_mul_complex_Ioi (a := ((-(a : Real) : Complex)))
      (by simpa using (neg_lt_zero.mpr ha)) 0
  have hprod : Integrable (Function.uncurry h)
      (volume.prod (volume.restrict (Ioi 0))) := by
    have hbase := hphi.mul_prod hexp
    apply hbase.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with z
      rw [Complex.norm_exp]
      simp
  have hinnerY (t : Real) :
      (∫ y : Real in Ioi 0, h t y) =
        phi t / ((a : Complex) + (t : Complex) * Complex.I) := by
    have hcoeff :
        (-((a : Complex) + (t : Complex) * Complex.I)).re < 0 := by
      simp
      exact ha
    calc
      (∫ y : Real in Ioi 0, h t y) =
          ∫ y : Real in Ioi 0,
            phi t * Complex.exp
              (-((a : Complex) + (t : Complex) * Complex.I) *
                (y : Complex)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        dsimp only [h]
        rw [mul_assoc]
        rw [← Complex.exp_add]
        congr 2
        ring
      _ = phi t * (∫ y : Real in Ioi 0,
            Complex.exp
              (-((a : Complex) + (t : Complex) * Complex.I) *
                (y : Complex))) := by
        rw [integral_const_mul]
      _ = phi t *
          (-Complex.exp
              (-((a : Complex) + (t : Complex) * Complex.I) * (0 : Real)) /
            -((a : Complex) + (t : Complex) * Complex.I)) := by
        rw [integral_exp_mul_complex_Ioi hcoeff]
      _ = phi t / ((a : Complex) + (t : Complex) * Complex.I) := by
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
          div_eq_mul_inv]
        rw [inv_neg]
        ring
  have hinnerT (y : Real) :
      (∫ t : Real, h t y) =
        (2 * (Real.pi : Complex)) *
          (Complex.exp ((-(a : Real) : Complex) * (y : Complex)) * psi y) := by
    calc
      (∫ t : Real, h t y) =
          ∫ t : Real,
            Complex.exp ((-(a : Real) : Complex) * (y : Complex)) *
              (phi t * Complex.exp
                (-((t : Complex) * (y : Complex) * Complex.I))) := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [h]
        ring
      _ = Complex.exp ((-(a : Real) : Complex) * (y : Complex)) *
          (∫ t : Real,
              phi t * Complex.exp
                (-((t : Complex) * (y : Complex) * Complex.I))) := by
        rw [integral_const_mul]
      _ = Complex.exp ((-(a : Real) : Complex) * (y : Complex)) *
          ((2 * (Real.pi : Complex)) * psi y) := by
        rw [hreadback]
      _ = (2 * (Real.pi : Complex)) *
          (Complex.exp ((-(a : Real) : Complex) * (y : Complex)) * psi y) := by
        ring
  have hinter : Integrable (fun t : Real =>
      ∫ y : Real in Ioi 0, h t y) :=
    hprod.integral_prod_left
  constructor
  · apply hinter.congr
    filter_upwards with t
    exact hinnerY t
  · calc
      (∫ t : Real,
          phi t / ((a : Complex) + (t : Complex) * Complex.I)) =
          ∫ t : Real,
            ∫ y : Real in Ioi 0, h t y := by
        apply integral_congr_ae
        filter_upwards with t
        exact (hinnerY t).symm
      _ = ∫ y : Real in Ioi 0,
          ∫ t : Real, h t y := by
        exact integral_integral_swap hprod
      _ = ∫ y : Real in Ioi 0,
          (2 * (Real.pi : Complex)) *
            (Complex.exp ((-(a : Real) : Complex) * (y : Complex)) * psi y) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        exact hinnerT y
      _ = (2 * (Real.pi : Complex)) *
          (∫ y : Real in Ioi 0,
            Complex.exp ((-(a : Real) : Complex) * (y : Complex)) * psi y) := by
        rw [integral_const_mul]

theorem integrable_fourierLaplace_div_vertical
    (f : TestFunction) {a : Real} (ha : 0 < a) :
    Integrable (fun t : Real =>
      fourierLaplace f t /
        ((a : Complex) + (t : Complex) * Complex.I)) :=
  (integrable_and_integral_mul_resolvent
    (fun t => fourierLaplace f t) f
    (integrable_fourierLaplace f)
    (fun y => integral_fourierLaplace_mul_character f y) ha).1

theorem integral_fourierLaplace_div_vertical
    (f : TestFunction) {a : Real} (ha : 0 < a) :
    (∫ t : Real,
      fourierLaplace f t /
        ((a : Complex) + (t : Complex) * Complex.I)) =
      (2 * (Real.pi : Complex)) *
        (∫ y : Real in Ioi 0,
          Complex.exp ((-(a : Real) : Complex) * (y : Complex)) * f y) :=
  (integrable_and_integral_mul_resolvent
    (fun t => fourierLaplace f t) f
    (integrable_fourierLaplace f)
    (fun y => integral_fourierLaplace_mul_character f y) ha).2

theorem integrable_fourierLaplace_neg_div_vertical
    (f : TestFunction) {a : Real} (ha : 0 < a) :
    Integrable (fun t : Real =>
      fourierLaplace f (-t) /
        ((a : Complex) + (t : Complex) * Complex.I)) := by
  have hreflected : Integrable (fun t : Real => fourierLaplace f (-t)) := by
    simpa only [neg_one_mul] using
      (integrable_fourierLaplace f).comp_mul_left'
        (R := (-1 : Real)) (by norm_num)
  exact (integrable_and_integral_mul_resolvent
    (fun t => fourierLaplace f (-t)) (fun y => f (-y))
    hreflected
    (fun y => integral_fourierLaplace_neg_mul_character f y) ha).1

theorem integral_fourierLaplace_neg_div_vertical
    (f : TestFunction) {a : Real} (ha : 0 < a) :
    (∫ t : Real,
      fourierLaplace f (-t) /
        ((a : Complex) + (t : Complex) * Complex.I)) =
      (2 * (Real.pi : Complex)) *
        (∫ y : Real in Ioi 0,
          Complex.exp ((-(a : Real) : Complex) * (y : Complex)) * f (-y)) := by
  have hreflected : Integrable (fun t : Real => fourierLaplace f (-t)) := by
    simpa only [neg_one_mul] using
      (integrable_fourierLaplace f).comp_mul_left'
        (R := (-1 : Real)) (by norm_num)
  exact (integrable_and_integral_mul_resolvent
    (fun t => fourierLaplace f (-t)) (fun y => f (-y))
    hreflected
    (fun y => integral_fourierLaplace_neg_mul_character f y) ha).2

private noncomputable def centerTwoPolePlusProfile
    (F : CompactLogTest) : TestFunction :=
  (CompactLogTest.exponentialWeight F
    (((3 / 2 : Real) : Complex))).test

private noncomputable def centerTwoPoleMinusProfile
    (F : CompactLogTest) : TestFunction :=
  (CompactLogTest.exponentialWeight F
    (((-3 / 2 : Real) : Complex))).test

private theorem symmetrizedLaplaceWeight_centerTwo_pole_eq
    (F : CompactLogTest) (t : Real) :
    symmetrizedLaplaceWeight F (verticalPoint 2 t) =
      fourierLaplace (centerTwoPolePlusProfile F) t +
        fourierLaplace (centerTwoPoleMinusProfile F) (-t) := by
  unfold symmetrizedLaplaceWeight
  rw [centeredLaplaceWeight_vertical_eq_fourierLaplace F 2 t]
  have hreflect :
      (1 : Complex) - verticalPoint 2 t = verticalPoint (-1) (-t) := by
    apply Complex.ext
    · simp [verticalPoint]
      ring
    · simp [verticalPoint]
  rw [hreflect]
  rw [centeredLaplaceWeight_vertical_eq_fourierLaplace F (-1) (-t)]
  simp only [centerTwoPolePlusProfile, centerTwoPoleMinusProfile]
  norm_num

/-! The following public readback keeps the center-`2` weight on its own
Fourier owner.  It is the inner transform needed by a later Gamma_R Fubini
argument; no archimedean distribution is folded into it here. -/

theorem integrable_symmetrizedLaplaceWeight_centerTwo_mul_character
    (F : CompactLogTest) (x : Real) :
    Integrable (fun t : Real =>
      symmetrizedLaplaceWeight F (verticalPoint 2 t) *
        Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) := by
  have hplus := integrable_fourierLaplace_mul_character
    (centerTwoPolePlusProfile F) x
  have hminus := integrable_fourierLaplace_neg_mul_character
    (centerTwoPoleMinusProfile F) x
  simpa only [symmetrizedLaplaceWeight_centerTwo_pole_eq, add_mul] using
    hplus.add hminus

theorem integral_symmetrizedLaplaceWeight_centerTwo_mul_character
    (F : CompactLogTest) (x : Real) :
    (∫ t : Real,
      symmetrizedLaplaceWeight F (verticalPoint 2 t) *
        Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) =
      (2 * (Real.pi : Complex)) *
        (Complex.exp (((3 / 2 : Real) : Complex) * (x : Complex)) *
          (F.test x + F.test (-x))) := by
  have hplusInt := integrable_fourierLaplace_mul_character
    (centerTwoPolePlusProfile F) x
  have hminusInt := integrable_fourierLaplace_neg_mul_character
    (centerTwoPoleMinusProfile F) x
  have hplus := integral_fourierLaplace_mul_character
    (centerTwoPolePlusProfile F) x
  have hminus := integral_fourierLaplace_neg_mul_character
    (centerTwoPoleMinusProfile F) x
  calc
    (∫ t : Real,
        symmetrizedLaplaceWeight F (verticalPoint 2 t) *
          Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) =
        ∫ t : Real,
          (fourierLaplace (centerTwoPolePlusProfile F) t +
            fourierLaplace (centerTwoPoleMinusProfile F) (-t)) *
            Complex.exp (-((t : Complex) * (x : Complex) * Complex.I)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [symmetrizedLaplaceWeight_centerTwo_pole_eq]
    _ = (∫ t : Real,
          fourierLaplace (centerTwoPolePlusProfile F) t *
            Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) +
        ∫ t : Real,
          fourierLaplace (centerTwoPoleMinusProfile F) (-t) *
            Complex.exp (-((t : Complex) * (x : Complex) * Complex.I)) := by
      rw [show (fun t : Real =>
          (fourierLaplace (centerTwoPolePlusProfile F) t +
            fourierLaplace (centerTwoPoleMinusProfile F) (-t)) *
            Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) =
          (fun t : Real =>
            fourierLaplace (centerTwoPolePlusProfile F) t *
                Complex.exp (-((t : Complex) * (x : Complex) * Complex.I)) +
              fourierLaplace (centerTwoPoleMinusProfile F) (-t) *
                Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) by
        funext t
        rw [add_mul]]
      exact integral_add hplusInt hminusInt
    _ = (2 * (Real.pi : Complex)) *
        (centerTwoPolePlusProfile F x +
          centerTwoPoleMinusProfile F (-x)) := by
      rw [hplus, hminus]
      ring
    _ = (2 * (Real.pi : Complex)) *
        (Complex.exp (((3 / 2 : Real) : Complex) * (x : Complex)) *
          (F.test x + F.test (-x))) := by
      simp only [centerTwoPolePlusProfile, centerTwoPoleMinusProfile,
        CompactLogTest.exponentialWeight_apply]
      have hminusExp :
          Complex.exp (((-3 / 2 : Real) : Complex) * ((-x : Real) : Complex)) =
            Complex.exp (((3 / 2 : Real) : Complex) * (x : Complex)) := by
        congr 1
        push_cast
        ring
      rw [hminusExp]
      ring

theorem integral_symmetrizedLaplaceWeight_centerTwo
    (F : CompactLogTest) :
    (∫ t : Real, symmetrizedLaplaceWeight F (verticalPoint 2 t)) =
      (4 * (Real.pi : Complex)) * F.test 0 := by
  have h := integral_symmetrizedLaplaceWeight_centerTwo_mul_character F 0
  calc
    (∫ t : Real, symmetrizedLaplaceWeight F (verticalPoint 2 t)) =
        (2 * (Real.pi : Complex)) * (F.test 0 + F.test 0) := by
      simpa using h
    _ = (4 * (Real.pi : Complex)) * F.test 0 := by
      ring

private theorem laplaceAt_real_eq_halfLines
    (F : CompactLogTest) (b : Real) :
    (∫ y : Real in Ioi 0,
        Complex.exp ((-b : Real) * (y : Complex)) * F.test (-y)) +
      (∫ y : Real in Ioi 0,
        Complex.exp ((b : Complex) * (y : Complex)) * F.test y) =
      CompactLogTest.laplaceAt F (b : Complex) := by
  let g : TestFunction :=
    (CompactLogTest.exponentialWeight F (b : Complex)).test
  have hnegative :
      (∫ y : Real in Ioi 0,
          Complex.exp ((-b : Real) * (y : Complex)) * F.test (-y)) =
        ∫ u : Real in Iic 0, g u := by
    calc
      (∫ y : Real in Ioi 0,
          Complex.exp ((-b : Real) * (y : Complex)) * F.test (-y)) =
          ∫ y : Real in Ioi 0, g (-y) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        simp only [g, CompactLogTest.exponentialWeight_apply]
        congr 2
        push_cast
        ring
      _ = ∫ u : Real in Iic 0, g u := by
        simp
  have hpositive :
      (∫ y : Real in Ioi 0,
          Complex.exp ((b : Complex) * (y : Complex)) * F.test y) =
        ∫ y : Real in Ioi 0, g y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [g, CompactLogTest.exponentialWeight_apply]
  calc
    (∫ y : Real in Ioi 0,
        Complex.exp ((-b : Real) * (y : Complex)) * F.test (-y)) +
        (∫ y : Real in Ioi 0,
          Complex.exp ((b : Complex) * (y : Complex)) * F.test y) =
        (∫ u : Real in Iic 0, g u) +
          ∫ y : Real in Ioi 0, g y := by
      rw [hnegative, hpositive]
    _ = ∫ u : Real, g u := by
      exact intervalIntegral.integral_Iic_add_Ioi
        g.integrable.integrableOn g.integrable.integrableOn
    _ = CompactLogTest.laplaceAt F (b : Complex) := by
      rfl

private theorem integrable_centerTwoWeight_div_vertical
    (F : CompactLogTest) {a : Real} (ha : 0 < a) :
    Integrable (fun t : Real =>
      symmetrizedLaplaceWeight F (verticalPoint 2 t) /
        ((a : Complex) + (t : Complex) * Complex.I)) := by
  have hplus := integrable_fourierLaplace_div_vertical
    (centerTwoPolePlusProfile F) ha
  have hminus := integrable_fourierLaplace_neg_div_vertical
    (centerTwoPoleMinusProfile F) ha
  simpa only [symmetrizedLaplaceWeight_centerTwo_pole_eq, add_div] using
    hplus.add hminus

private theorem integral_centerTwoWeight_div_vertical
    (F : CompactLogTest) {a : Real} (ha : 0 < a) :
    (∫ t : Real,
      symmetrizedLaplaceWeight F (verticalPoint 2 t) /
        ((a : Complex) + (t : Complex) * Complex.I)) =
      (2 * (Real.pi : Complex)) *
        ((∫ y : Real in Ioi 0,
            Complex.exp (-(a : Complex) * (y : Complex)) *
              centerTwoPolePlusProfile F y) +
          (∫ y : Real in Ioi 0,
            Complex.exp (-(a : Complex) * (y : Complex)) *
              centerTwoPoleMinusProfile F (-y))) := by
  have hplus := integrable_fourierLaplace_div_vertical
    (centerTwoPolePlusProfile F) ha
  have hminus := integrable_fourierLaplace_neg_div_vertical
    (centerTwoPoleMinusProfile F) ha
  calc
    (∫ t : Real,
        symmetrizedLaplaceWeight F (verticalPoint 2 t) /
          ((a : Complex) + (t : Complex) * Complex.I)) =
        (∫ t : Real,
          fourierLaplace (centerTwoPolePlusProfile F) t /
              ((a : Complex) + (t : Complex) * Complex.I) +
            fourierLaplace (centerTwoPoleMinusProfile F) (-t) /
              ((a : Complex) + (t : Complex) * Complex.I)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [symmetrizedLaplaceWeight_centerTwo_pole_eq]
      ring
    _ = (∫ t : Real,
          fourierLaplace (centerTwoPolePlusProfile F) t /
            ((a : Complex) + (t : Complex) * Complex.I)) +
        (∫ t : Real,
          fourierLaplace (centerTwoPoleMinusProfile F) (-t) /
            ((a : Complex) + (t : Complex) * Complex.I)) := by
      rw [integral_add hplus hminus]
    _ = (2 * (Real.pi : Complex)) *
          (∫ y : Real in Ioi 0,
            Complex.exp (-(a : Complex) * (y : Complex)) *
              centerTwoPolePlusProfile F y) +
        (2 * (Real.pi : Complex)) *
          (∫ y : Real in Ioi 0,
            Complex.exp (-(a : Complex) * (y : Complex)) *
              centerTwoPoleMinusProfile F (-y)) := by
      rw [integral_fourierLaplace_div_vertical _ ha,
        integral_fourierLaplace_neg_div_vertical _ ha]
    _ = (2 * (Real.pi : Complex)) *
        ((∫ y : Real in Ioi 0,
            Complex.exp (-(a : Complex) * (y : Complex)) *
              centerTwoPolePlusProfile F y) +
          (∫ y : Real in Ioi 0,
            Complex.exp (-(a : Complex) * (y : Complex)) *
              centerTwoPoleMinusProfile F (-y))) := by
      ring

private theorem centerTwo_resolvent_sum_eq_poleLaplace
    (F : CompactLogTest) :
    (∫ t : Real,
        symmetrizedLaplaceWeight F (verticalPoint 2 t) /
          (((2 : Real) : Complex) + (t : Complex) * Complex.I)) +
      (∫ t : Real,
        symmetrizedLaplaceWeight F (verticalPoint 2 t) /
          (((1 : Real) : Complex) + (t : Complex) * Complex.I)) =
      (2 * (Real.pi : Complex)) *
        (CompactLogTest.laplaceAt F (1 / 2 : Complex) +
          CompactLogTest.laplaceAt F (-(1 / 2 : Complex))) := by
  have htwo := integral_centerTwoWeight_div_vertical F
    (a := (2 : Real)) (by norm_num)
  have hone := integral_centerTwoWeight_div_vertical F
    (a := (1 : Real)) (by norm_num)
  have htwoPlus :
      (∫ y : Real in Ioi 0,
          Complex.exp (-((2 : Real) : Complex) * (y : Complex)) *
            centerTwoPolePlusProfile F y) =
        ∫ y : Real in Ioi 0,
          Complex.exp (-((1 / 2 : Complex) * (y : Complex))) *
            F.test y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [centerTwoPolePlusProfile,
      CompactLogTest.exponentialWeight_apply]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have htwoMinus :
      (∫ y : Real in Ioi 0,
          Complex.exp (-((2 : Real) : Complex) * (y : Complex)) *
            centerTwoPoleMinusProfile F (-y)) =
        ∫ y : Real in Ioi 0,
          Complex.exp (-((1 / 2 : Complex) * (y : Complex))) *
            F.test (-y) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [centerTwoPoleMinusProfile,
      CompactLogTest.exponentialWeight_apply]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have honePlus :
      (∫ y : Real in Ioi 0,
          Complex.exp (-((1 : Real) : Complex) * (y : Complex)) *
            centerTwoPolePlusProfile F y) =
        ∫ y : Real in Ioi 0,
          Complex.exp ((1 / 2 : Complex) * (y : Complex)) *
            F.test y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [centerTwoPolePlusProfile,
      CompactLogTest.exponentialWeight_apply]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have honeMinus :
      (∫ y : Real in Ioi 0,
          Complex.exp (-((1 : Real) : Complex) * (y : Complex)) *
            centerTwoPoleMinusProfile F (-y)) =
        ∫ y : Real in Ioi 0,
          Complex.exp ((1 / 2 : Complex) * (y : Complex)) *
            F.test (-y) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [centerTwoPoleMinusProfile,
      CompactLogTest.exponentialWeight_apply]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hlaplacePlus := laplaceAt_real_eq_halfLines F (1 / 2 : Real)
  have hlaplaceMinus := laplaceAt_real_eq_halfLines F (-1 / 2 : Real)
  rw [htwo, hone, htwoPlus, htwoMinus, honePlus, honeMinus]
  rw [← mul_add]
  congr 1
  calc
    ((∫ y : Real in Ioi 0,
          Complex.exp (-((1 / 2 : Complex) * (y : Complex))) *
            F.test y) +
        (∫ y : Real in Ioi 0,
          Complex.exp (-((1 / 2 : Complex) * (y : Complex))) *
            F.test (-y))) +
      ((∫ y : Real in Ioi 0,
          Complex.exp ((1 / 2 : Complex) * (y : Complex)) *
            F.test y) +
        (∫ y : Real in Ioi 0,
          Complex.exp ((1 / 2 : Complex) * (y : Complex)) *
            F.test (-y))) =
        ((∫ y : Real in Ioi 0,
            Complex.exp (-((1 / 2 : Complex) * (y : Complex))) *
              F.test (-y)) +
          (∫ y : Real in Ioi 0,
            Complex.exp ((1 / 2 : Complex) * (y : Complex)) *
              F.test y)) +
        ((∫ y : Real in Ioi 0,
            Complex.exp ((1 / 2 : Complex) * (y : Complex)) *
              F.test (-y)) +
          (∫ y : Real in Ioi 0,
            Complex.exp (-((1 / 2 : Complex) * (y : Complex))) *
              F.test y)) := by
      ring
    _ = CompactLogTest.laplaceAt F (1 / 2 : Complex) +
        CompactLogTest.laplaceAt F (-(1 / 2 : Complex)) := by
      norm_num at hlaplacePlus hlaplaceMinus
      exact congrArg₂ (fun x y : Complex => x + y)
        hlaplacePlus hlaplaceMinus

/-- The center-`2` elementary-pole integrand is integrable on the full real
line. -/
theorem integrable_elementaryPoleIntegrand_centerTwo
    (F : CompactLogTest) :
    Integrable (fun t : Real => elementaryPoleIntegrand F 2 t) := by
  have htwo := integrable_centerTwoWeight_div_vertical F
    (a := (2 : Real)) (by norm_num)
  have hone := integrable_centerTwoWeight_div_vertical F
    (a := (1 : Real)) (by norm_num)
  rw [show (fun t : Real => elementaryPoleIntegrand F 2 t) =
      (fun t : Real =>
        -((symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              (((2 : Real) : Complex) + (t : Complex) * Complex.I)) +
          (symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              (((1 : Real) : Complex) + (t : Complex) * Complex.I))) *
            Complex.I) by
    funext t
    unfold elementaryPoleIntegrand
    norm_num [verticalPoint]
    ring]
  exact (htwo.add hone).neg.mul_const Complex.I

/-- The complete center-`2` elementary-pole integral is the negative pole
owner in the contour normalization. -/
theorem integral_elementaryPoleIntegrand_centerTwo_eq
    (F : CompactLogTest) :
    (∫ t : Real, elementaryPoleIntegrand F 2 t) =
      -(2 * (Real.pi : Complex) * Complex.I) *
        (CompactLogTest.laplaceAt F (1 / 2 : Complex) +
          CompactLogTest.laplaceAt F (-(1 / 2 : Complex))) := by
  have htwo := integrable_centerTwoWeight_div_vertical F
    (a := (2 : Real)) (by norm_num)
  have hone := integrable_centerTwoWeight_div_vertical F
    (a := (1 : Real)) (by norm_num)
  calc
    (∫ t : Real, elementaryPoleIntegrand F 2 t) =
        ∫ t : Real,
          -((symmetrizedLaplaceWeight F (verticalPoint 2 t) /
                (((2 : Real) : Complex) + (t : Complex) * Complex.I)) +
            (symmetrizedLaplaceWeight F (verticalPoint 2 t) /
                (((1 : Real) : Complex) + (t : Complex) * Complex.I))) * Complex.I := by
      apply integral_congr_ae
      filter_upwards with t
      unfold elementaryPoleIntegrand
      norm_num [verticalPoint]
      ring
    _ = -((∫ t : Real,
          symmetrizedLaplaceWeight F (verticalPoint 2 t) /
            (((2 : Real) : Complex) + (t : Complex) * Complex.I)) +
        (∫ t : Real,
          symmetrizedLaplaceWeight F (verticalPoint 2 t) /
            (((1 : Real) : Complex) + (t : Complex) * Complex.I))) * Complex.I := by
      rw [integral_mul_const, integral_neg, integral_add htwo hone]
    _ = -(2 * (Real.pi : Complex) * Complex.I) *
        (CompactLogTest.laplaceAt F (1 / 2 : Complex) +
          CompactLogTest.laplaceAt F (-(1 / 2 : Complex))) := by
      rw [centerTwo_resolvent_sum_eq_poleLaplace F]
      ring

theorem normalized_integral_elementaryPole_centerTwo_eq
    (F : CompactLogTest) :
    ((2 * (Real.pi : Complex) * Complex.I)⁻¹) *
        (∫ t : Real, elementaryPoleIntegrand F 2 t) =
      -(CompactLogTest.laplaceAt F (1 / 2 : Complex) +
        CompactLogTest.laplaceAt F (-(1 / 2 : Complex))) := by
  have hK : (2 * (Real.pi : Complex) * Complex.I) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [integral_elementaryPoleIntegrand_centerTwo_eq]
  calc
    (2 * (Real.pi : Complex) * Complex.I)⁻¹ *
        (-(2 * (Real.pi : Complex) * Complex.I) *
          (CompactLogTest.laplaceAt F (1 / 2 : Complex) +
            CompactLogTest.laplaceAt F (-(1 / 2 : Complex)))) =
        -((2 * (Real.pi : Complex) * Complex.I)⁻¹ *
          (2 * (Real.pi : Complex) * Complex.I)) *
            (CompactLogTest.laplaceAt F (1 / 2 : Complex) +
              CompactLogTest.laplaceAt F (-(1 / 2 : Complex))) := by
      ring
    _ = -(CompactLogTest.laplaceAt F (1 / 2 : Complex) +
        CompactLogTest.laplaceAt F (-(1 / 2 : Complex))) := by
      rw [inv_mul_cancel₀ hK, neg_one_mul]

theorem normalized_integral_elementaryPole_centerTwo_re_eq
    (F : CompactLogTest) :
    ((((2 * (Real.pi : Complex) * Complex.I)⁻¹) *
      (∫ t : Real, elementaryPoleIntegrand F 2 t)).re) =
        -poleTerm F := by
  rw [normalized_integral_elementaryPole_centerTwo_eq]
  have hhalf : -(1 / 2 : Complex) = (-1 / 2 : Complex) := by
    ring
  rw [hhalf]
  simp [poleTerm]

/-- Symmetric selected-height intervals converge to the full center-`2`
elementary-pole integral. -/
theorem tendsto_selected_intervalIntegral_elementaryPole_centerTwo
    (F : CompactLogTest) {height : Nat -> Real}
    (hheight : Tendsto height atTop atTop) :
    Tendsto
      (fun n : Nat => ∫ t : Real in (-height n)..height n,
        elementaryPoleIntegrand F 2 t)
      atTop
      (nhds (∫ t : Real, elementaryPoleIntegrand F 2 t)) := by
  have hneg : Tendsto (fun n : Nat => -height n) atTop atBot :=
    by simpa only [mul_neg, mul_one] using
      hheight.atTop_mul_const_of_neg' (by norm_num : (-1 : Real) < 0)
  exact intervalIntegral_tendsto_integral
    (integrable_elementaryPoleIntegrand_centerTwo F) hneg hheight

end
end C1XiCenterTwoPole
end Source
end ConnesWeilRH
