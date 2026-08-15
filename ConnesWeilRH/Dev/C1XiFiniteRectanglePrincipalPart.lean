import ConnesWeilRH.Dev.C1XiFiniteRectangleBoundary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# C1XiFiniteRectanglePrincipalPart - finite xi principal parts on rectangles

This module begins the missing principal-part readout after the regularized
xi contour kernel has been removed from a rectangle boundary.  It fixes the
standard rectangle orientation and proves the exterior half of the one-pole
residue calculation: a simple pole outside the closed rectangle has zero
boundary integral by Cauchy-Goursat.

The centered-square interior one-pole value is computed directly from the four
real edge integrals.  The general strict-interior rectangle and the finite-pole
sum remain separate work.
No contour limit, arithmetic readback, explicit-formula equality, or RH claim
is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteRectanglePrincipalPart

open Set
open MeasureTheory
open Filter
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1XiFiniteRectangleBoundary
open C1XiFiniteFactor
open C1XiFiniteRegularization
open C1XiVerticalFunctional
open scoped BigOperators Interval Topology

/-- A rectangle is in the standard positive orientation when its first corner
is lower-left and its second corner is upper-right. -/
def standardRectangle (z w : Complex) : Prop :=
  z.re < w.re ∧ z.im < w.im

/-- A point lies strictly inside a standard axis-parallel rectangle.  This
excludes all four boundary edges, which is the geometric condition needed by
the later finite-pole residue readout. -/
def strictlyInsideRectangle (z w u : Complex) : Prop :=
  z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im

/-- The finite divisor support of one factor owner avoids the rectangle
boundary.  The four clauses speak about the actual closed edge segments, not
their full supporting lines; this is exactly what makes every principal-pole
edge integral legitimate. -/
def rectangleBoundaryAvoidsFiniteSupport (c : Complex) (R : Real)
    (z w : Complex) : Prop :=
  (∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
    ∀ x ∈ [[z.re, w.re]], (x : Complex) + z.im * Complex.I ≠ u) ∧
  (∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
    ∀ x ∈ [[z.re, w.re]], (x : Complex) + w.im * Complex.I ≠ u) ∧
  (∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
    ∀ y ∈ [[z.im, w.im]], (w.re : Complex) + y * Complex.I ≠ u) ∧
  ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
    ∀ y ∈ [[z.im, w.im]], (z.re : Complex) + y * Complex.I ≠ u

/-- The unweighted simple principal pole used to isolate the geometric
rectangle-residue calculation from the xi multiplicity and Laplace weight. -/
noncomputable def rectangleSimplePole (u z : Complex) : Complex :=
  (z - u)⁻¹

theorem differentiableAt_rectangleSimplePole_of_ne {u z : Complex} (hzu : z ≠ u) :
    DifferentiableAt Complex (rectangleSimplePole u) z := by
  unfold rectangleSimplePole
  exact (differentiableAt_id.sub (differentiable_const (c := u)).differentiableAt).inv
    (sub_ne_zero.mpr hzu)

/-- The boundary integral of a single simple pole vanishes whenever the pole
is outside the entire closed rectangle.  This is the exterior half of the
rectangle residue theorem, obtained legally from Cauchy-Goursat because the
integrand is differentiable on the full closed rectangle. -/
theorem xiRectangleBoundaryIntegral_rectangleSimplePole_eq_zero_of_not_mem_rectangle
    {z w u : Complex} (hu : u ∉ Complex.Rectangle z w) :
    xiRectangleBoundaryIntegral (rectangleSimplePole u) z w = 0 := by
  apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn
  intro q hq
  apply (differentiableAt_rectangleSimplePole_of_ne (u := u) ?_).differentiableWithinAt
  intro hqu
  apply hu
  simpa [hqu] using hq

private theorem rectangleSimplePole_bottom_sub_top (u : Complex) {r : Real} (hr : 0 < r)
    (x : Real) :
    rectangleSimplePole u ((x : Complex) + (u.im - r) * Complex.I) -
      rectangleSimplePole u ((x : Complex) + (u.im + r) * Complex.I) =
        ((2 * r / ((x - u.re) ^ 2 + r ^ 2) : Real) : Complex) * Complex.I := by
  have hbottom : (x : Complex) + (u.im - r) * Complex.I - u =
      ((x - u.re : Real) : Complex) - r * Complex.I := by
    apply Complex.ext <;> simp
  have htop : (x : Complex) + (u.im + r) * Complex.I - u =
      ((x - u.re : Real) : Complex) + r * Complex.I := by
    apply Complex.ext <;> simp
  have hbottom0 : ((x - u.re : Real) : Complex) - r * Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have : -r = 0 := by simpa using him
    exact hr.ne' (neg_eq_zero.mp this)
  have htop0 : ((x - u.re : Real) : Complex) + r * Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have : r = 0 := by simpa using him
    exact hr.ne' this
  rw [rectangleSimplePole, rectangleSimplePole, hbottom, htop, inv_sub_inv hbottom0 htop0]
  rw [show (((x - u.re : Real) : Complex) + r * Complex.I) -
      (((x - u.re : Real) : Complex) - r * Complex.I) = 2 * r * Complex.I by ring]
  have hproduct : ((((x - u.re : Real) : Complex) - r * Complex.I) *
      (((x - u.re : Real) : Complex) + r * Complex.I)) =
      (((x - u.re) ^ 2 + r ^ 2 : Real) : Complex) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hproduct]
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  push_cast
  ring

private theorem rectangleSimplePole_right_sub_left (u : Complex) {r : Real} (hr : 0 < r)
    (y : Real) :
    rectangleSimplePole u ((u.re + r : Real) + y * Complex.I) -
      rectangleSimplePole u ((u.re - r : Real) + y * Complex.I) =
        ((2 * r / ((y - u.im) ^ 2 + r ^ 2) : Real) : Complex) := by
  have hright : (u.re + r : Real) + y * Complex.I - u =
      (r : Complex) + ((y - u.im : Real) : Complex) * Complex.I := by
    apply Complex.ext <;> simp
  have hleft : (u.re - r : Real) + y * Complex.I - u =
      -(r : Complex) + ((y - u.im : Real) : Complex) * Complex.I := by
    apply Complex.ext <;> simp
  have hright0 : (r : Complex) + ((y - u.im : Real) : Complex) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have : r = 0 := by simpa using hre
    exact hr.ne' this
  have hleft0 : -(r : Complex) + ((y - u.im : Real) : Complex) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have : -r = 0 := by simpa using hre
    exact hr.ne' (neg_eq_zero.mp this)
  rw [rectangleSimplePole, rectangleSimplePole, hright, hleft, inv_sub_inv hright0 hleft0]
  rw [show ((-(r : Complex) + ((y - u.im : Real) : Complex) * Complex.I) -
      ((r : Complex) + ((y - u.im : Real) : Complex) * Complex.I)) = -2 * r by ring]
  have hproduct : ((r : Complex) + ((y - u.im : Real) : Complex) * Complex.I) *
      (-(r : Complex) + ((y - u.im : Real) : Complex) * Complex.I) =
      -(((y - u.im) ^ 2 + r ^ 2 : Real) : Complex) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hproduct]
  rw [div_eq_mul_inv, inv_neg, ← Complex.ofReal_inv]
  push_cast
  ring

private theorem integral_two_mul_cauchy_density (r : Real) (hr : 0 < r) :
    (∫ x : Real in -r..r, 2 * r / (x ^ 2 + r ^ 2)) = Real.pi := by
  have hr0 : r ≠ 0 := hr.ne'
  have hrewrite : (fun x : Real => 2 * r / (x ^ 2 + r ^ 2)) =
      fun x => 2 * (r / (r ^ 2 + x ^ 2)) := by
    funext x
    rw [add_comm (x ^ 2) (r ^ 2)]
    ring
  rw [hrewrite, intervalIntegral.integral_const_mul, integral_div_sq_add_sq]
  rw [neg_div, div_self hr0, Real.arctan_neg, Real.arctan_one]
  ring

private theorem integral_two_mul_cauchy_density_shifted (center r : Real) (hr : 0 < r) :
    (∫ x : Real in center - r..center + r,
      2 * r / ((x - center) ^ 2 + r ^ 2)) = Real.pi := by
  calc
    (∫ x : Real in center - r..center + r,
      2 * r / ((x - center) ^ 2 + r ^ 2)) =
        ∫ x : Real in -r..r, 2 * r / (x ^ 2 + r ^ 2) := by
      convert intervalIntegral.integral_comp_sub_right
        (f := fun x : Real => 2 * r / (x ^ 2 + r ^ 2))
        (a := center - r) (b := center + r) center using 1 <;> ring
    _ = Real.pi := integral_two_mul_cauchy_density r hr

private theorem intervalIntegrable_rectangleSimplePole_bottom (u : Complex) {r : Real}
    (hr : 0 < r) :
    IntervalIntegrable
      (fun x : Real => rectangleSimplePole u ((x : Complex) + (u.im - r) * Complex.I))
      volume (u.re - r) (u.re + r) := by
  apply Continuous.intervalIntegrable
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hne : (x : Complex) + (u.im - r) * Complex.I - u ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have : -r = 0 := by simpa using him
    exact hr.ne' (neg_eq_zero.mp this)
  have hz_ne : (x : Complex) + (u.im - r) * Complex.I ≠ u := sub_ne_zero.mp hne
  have hpath : ContinuousAt
      (fun x : Real => (x : Complex) + (u.im - r) * Complex.I) x := by
    fun_prop
  have hcomp : ContinuousAt
      (rectangleSimplePole u ∘ fun x : Real => (x : Complex) + (u.im - r) * Complex.I) x :=
    ContinuousAt.comp (f := fun x : Real =>
      (x : Complex) + (u.im - r) * Complex.I)
      (differentiableAt_rectangleSimplePole_of_ne hz_ne).continuousAt hpath
  simpa only [Function.comp_apply] using hcomp

private theorem intervalIntegrable_rectangleSimplePole_top (u : Complex) {r : Real}
    (hr : 0 < r) :
    IntervalIntegrable
      (fun x : Real => rectangleSimplePole u ((x : Complex) + (u.im + r) * Complex.I))
      volume (u.re - r) (u.re + r) := by
  apply Continuous.intervalIntegrable
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hne : (x : Complex) + (u.im + r) * Complex.I - u ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have : r = 0 := by simpa using him
    exact hr.ne' this
  have hz_ne : (x : Complex) + (u.im + r) * Complex.I ≠ u := sub_ne_zero.mp hne
  have hpath : ContinuousAt
      (fun x : Real => (x : Complex) + (u.im + r) * Complex.I) x := by
    fun_prop
  have hcomp : ContinuousAt
      (rectangleSimplePole u ∘ fun x : Real => (x : Complex) + (u.im + r) * Complex.I) x :=
    ContinuousAt.comp (f := fun x : Real =>
      (x : Complex) + (u.im + r) * Complex.I)
      (differentiableAt_rectangleSimplePole_of_ne hz_ne).continuousAt hpath
  simpa only [Function.comp_apply] using hcomp

private theorem intervalIntegrable_rectangleSimplePole_right (u : Complex) {r : Real}
    (hr : 0 < r) :
    IntervalIntegrable
      (fun y : Real => rectangleSimplePole u ((u.re + r : Real) + y * Complex.I))
      volume (u.im - r) (u.im + r) := by
  apply Continuous.intervalIntegrable
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hne : (u.re + r : Real) + y * Complex.I - u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have : r = 0 := by simpa using hre
    exact hr.ne' this
  have hz_ne : (u.re + r : Real) + y * Complex.I ≠ u := sub_ne_zero.mp hne
  have hpath : ContinuousAt
      (fun y : Real => (u.re + r : Real) + y * Complex.I) y := by
    fun_prop
  have hcomp : ContinuousAt
      (rectangleSimplePole u ∘ fun y : Real => (u.re + r : Real) + y * Complex.I) y :=
    ContinuousAt.comp (f := fun y : Real =>
      (u.re + r : Real) + y * Complex.I)
      (differentiableAt_rectangleSimplePole_of_ne hz_ne).continuousAt hpath
  simpa only [Function.comp_apply] using hcomp

private theorem intervalIntegrable_rectangleSimplePole_left (u : Complex) {r : Real}
    (hr : 0 < r) :
    IntervalIntegrable
      (fun y : Real => rectangleSimplePole u ((u.re - r : Real) + y * Complex.I))
      volume (u.im - r) (u.im + r) := by
  apply Continuous.intervalIntegrable
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hne : (u.re - r : Real) + y * Complex.I - u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have : -r = 0 := by simpa using hre
    exact hr.ne' (neg_eq_zero.mp this)
  have hz_ne : (u.re - r : Real) + y * Complex.I ≠ u := sub_ne_zero.mp hne
  have hpath : ContinuousAt
      (fun y : Real => (u.re - r : Real) + y * Complex.I) y := by
    fun_prop
  have hcomp : ContinuousAt
      (rectangleSimplePole u ∘ fun y : Real => (u.re - r : Real) + y * Complex.I) y :=
    ContinuousAt.comp (f := fun y : Real =>
      (u.re - r : Real) + y * Complex.I)
      (differentiableAt_rectangleSimplePole_of_ne hz_ne).continuousAt hpath
  simpa only [Function.comp_apply] using hcomp

/-- A positive-oriented square centered at the pole has the expected simple
residue.  The proof is an explicit real-line computation of the four edges;
no rectangle Cauchy theorem is applied across the pole. -/
theorem xiRectangleBoundaryIntegral_rectangleSimplePole_eq_two_pi_I_of_center
    {u : Complex} {r : Real} (hr : 0 < r) :
    xiRectangleBoundaryIntegral (rectangleSimplePole u)
        ((u.re - r : Real) + (u.im - r) * Complex.I)
        ((u.re + r : Real) + (u.im + r) * Complex.I) =
      2 * (Real.pi : Complex) * Complex.I := by
  have hbottom_int := intervalIntegrable_rectangleSimplePole_bottom u hr
  have htop_int := intervalIntegrable_rectangleSimplePole_top u hr
  have hright_int := intervalIntegrable_rectangleSimplePole_right u hr
  have hleft_int := intervalIntegrable_rectangleSimplePole_left u hr
  have hbottom_top :
      (∫ x : Real in u.re - r..u.re + r,
        rectangleSimplePole u ((x : Complex) + (u.im - r) * Complex.I)) -
        ∫ x : Real in u.re - r..u.re + r,
          rectangleSimplePole u ((x : Complex) + (u.im + r) * Complex.I) =
        Real.pi * Complex.I := by
    calc
      _ = ∫ x : Real in u.re - r..u.re + r,
          (rectangleSimplePole u ((x : Complex) + (u.im - r) * Complex.I) -
            rectangleSimplePole u ((x : Complex) + (u.im + r) * Complex.I)) :=
        (intervalIntegral.integral_sub hbottom_int htop_int).symm
      _ = ∫ x : Real in u.re - r..u.re + r,
          (((2 * r / ((x - u.re) ^ 2 + r ^ 2) : Real) : Complex) * Complex.I) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact rectangleSimplePole_bottom_sub_top u hr x
      _ = (∫ x : Real in u.re - r..u.re + r,
          ((2 * r / ((x - u.re) ^ 2 + r ^ 2) : Real) : Complex)) * Complex.I := by
        rw [intervalIntegral.integral_mul_const]
      _ = Real.pi * Complex.I := by
        rw [intervalIntegral.integral_ofReal, integral_two_mul_cauchy_density_shifted u.re r hr]
  have hright_left :
      (∫ y : Real in u.im - r..u.im + r,
        rectangleSimplePole u ((u.re + r : Real) + y * Complex.I)) -
        ∫ y : Real in u.im - r..u.im + r,
          rectangleSimplePole u ((u.re - r : Real) + y * Complex.I) =
        (Real.pi : Complex) := by
    calc
      _ = ∫ y : Real in u.im - r..u.im + r,
          (rectangleSimplePole u ((u.re + r : Real) + y * Complex.I) -
            rectangleSimplePole u ((u.re - r : Real) + y * Complex.I)) :=
        (intervalIntegral.integral_sub hright_int hleft_int).symm
      _ = ∫ y : Real in u.im - r..u.im + r,
          (((2 * r / ((y - u.im) ^ 2 + r ^ 2) : Real) : Complex)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact rectangleSimplePole_right_sub_left u hr y
      _ = (Real.pi : Complex) := by
        rw [intervalIntegral.integral_ofReal, integral_two_mul_cauchy_density_shifted u.im r hr]
  let rightEdge : Complex := ∫ y : Real in u.im - r..u.im + r,
    rectangleSimplePole u ((u.re : Complex) + r + y * Complex.I)
  let leftEdge : Complex := ∫ y : Real in u.im - r..u.im + r,
    rectangleSimplePole u ((u.re : Complex) - r + y * Complex.I)
  have hright_left_normalized : rightEdge - leftEdge = (Real.pi : Complex) := by
    simpa only [rightEdge, leftEdge, Complex.ofReal_add, Complex.ofReal_sub] using hright_left
  have hzre : (((u.re - r : Real) + (u.im - r) * Complex.I) : Complex).re = u.re - r := by
    simp
  have hwre : (((u.re + r : Real) + (u.im + r) * Complex.I) : Complex).re = u.re + r := by
    simp
  have hzim : (((u.re - r : Real) + (u.im - r) * Complex.I) : Complex).im = u.im - r := by
    simp
  have hwim : (((u.re + r : Real) + (u.im + r) * Complex.I) : Complex).im = u.im + r := by
    simp
  unfold xiRectangleBoundaryIntegral
  simp only [smul_eq_mul]
  rw [hzre, hwre, hzim, hwim]
  simp only [Complex.ofReal_add, Complex.ofReal_sub]
  rw [hbottom_top]
  change ((Real.pi : Complex) * Complex.I + Complex.I * rightEdge) -
      Complex.I * leftEdge = 2 * (Real.pi : Complex) * Complex.I
  linear_combination Complex.I * hright_left_normalized

/-- The same oriented rectangle boundary integral with its four real
coordinates made explicit.  This private spelling makes strip cancellation
literal: adjacent rectangles share an entire edge with opposite orientation. -/
private noncomputable def rectangleBoundaryIntegralCoords
    (f : Complex -> Complex) (left right bottom top : Real) : Complex :=
  (∫ x : Real in left..right, f ((x : Complex) + bottom * Complex.I)) -
    (∫ x : Real in left..right, f ((x : Complex) + top * Complex.I)) +
    Complex.I • (∫ y : Real in bottom..top, f ((right : Complex) + y * Complex.I)) -
    Complex.I • (∫ y : Real in bottom..top, f ((left : Complex) + y * Complex.I))

private theorem xiRectangleBoundaryIntegral_eq_coords
    (f : Complex -> Complex) (left right bottom top : Real) :
    xiRectangleBoundaryIntegral f
        ((left : Complex) + bottom * Complex.I)
        ((right : Complex) + top * Complex.I) =
      rectangleBoundaryIntegralCoords f left right bottom top := by
  unfold xiRectangleBoundaryIntegral rectangleBoundaryIntegralCoords
  simp

private theorem mem_complexRectangle_coords_iff
    (q : Complex) (left right bottom top : Real) :
    q ∈ Complex.Rectangle
        ((left : Complex) + bottom * Complex.I)
        ((right : Complex) + top * Complex.I) ↔
      q.re ∈ [[left, right]] ∧ q.im ∈ [[bottom, top]] := by
  rw [Complex.Rectangle, Complex.mem_reProdIm]
  simp

/-- Expanding a rectangle to the left changes its boundary by the boundary of
the added strip.  The statement is purely oriented-edge algebra. -/
private theorem rectangleBoundaryIntegralCoords_expand_left
    (f : Complex -> Complex) {left split right bottom top : Real}
    (hstrip : rectangleBoundaryIntegralCoords f left split bottom top = 0)
    (hbottom_left : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + bottom * Complex.I)) volume left split)
    (hbottom_right : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + bottom * Complex.I)) volume split right)
    (htop_left : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + top * Complex.I)) volume left split)
    (htop_right : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + top * Complex.I)) volume split right) :
    rectangleBoundaryIntegralCoords f left right bottom top =
      rectangleBoundaryIntegralCoords f split right bottom top := by
  unfold rectangleBoundaryIntegralCoords at hstrip ⊢
  simp only [smul_eq_mul] at hstrip ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals hbottom_left hbottom_right]
  rw [← intervalIntegral.integral_add_adjacent_intervals htop_left htop_right]
  linear_combination hstrip

/-- Expanding a rectangle to the right changes its boundary by the boundary of
the added strip.  The shared vertical edge cancels with its opposite
orientation. -/
private theorem rectangleBoundaryIntegralCoords_expand_right
    (f : Complex -> Complex) {left split right bottom top : Real}
    (hstrip : rectangleBoundaryIntegralCoords f split right bottom top = 0)
    (hbottom_left : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + bottom * Complex.I)) volume left split)
    (hbottom_right : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + bottom * Complex.I)) volume split right)
    (htop_left : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + top * Complex.I)) volume left split)
    (htop_right : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + top * Complex.I)) volume split right) :
    rectangleBoundaryIntegralCoords f left right bottom top =
      rectangleBoundaryIntegralCoords f left split bottom top := by
  unfold rectangleBoundaryIntegralCoords at hstrip ⊢
  simp only [smul_eq_mul] at hstrip ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals hbottom_left hbottom_right]
  rw [← intervalIntegral.integral_add_adjacent_intervals htop_left htop_right]
  linear_combination hstrip

/-- Expanding a rectangle downward changes its boundary by the lower strip.
Only the vertical edge integrals need to be split. -/
private theorem rectangleBoundaryIntegralCoords_expand_bottom
    (f : Complex -> Complex) {left right bottom split top : Real}
    (hstrip : rectangleBoundaryIntegralCoords f left right bottom split = 0)
    (hright_bottom : IntervalIntegrable
      (fun y : Real => f ((right : Complex) + y * Complex.I)) volume bottom split)
    (hright_top : IntervalIntegrable
      (fun y : Real => f ((right : Complex) + y * Complex.I)) volume split top)
    (hleft_bottom : IntervalIntegrable
      (fun y : Real => f ((left : Complex) + y * Complex.I)) volume bottom split)
    (hleft_top : IntervalIntegrable
      (fun y : Real => f ((left : Complex) + y * Complex.I)) volume split top) :
    rectangleBoundaryIntegralCoords f left right bottom top =
      rectangleBoundaryIntegralCoords f left right split top := by
  unfold rectangleBoundaryIntegralCoords at hstrip ⊢
  simp only [smul_eq_mul] at hstrip ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals hright_bottom hright_top]
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft_bottom hleft_top]
  linear_combination hstrip

/-- Expanding a rectangle upward changes its boundary by the upper strip. -/
private theorem rectangleBoundaryIntegralCoords_expand_top
    (f : Complex -> Complex) {left right bottom split top : Real}
    (hstrip : rectangleBoundaryIntegralCoords f left right split top = 0)
    (hright_bottom : IntervalIntegrable
      (fun y : Real => f ((right : Complex) + y * Complex.I)) volume bottom split)
    (hright_top : IntervalIntegrable
      (fun y : Real => f ((right : Complex) + y * Complex.I)) volume split top)
    (hleft_bottom : IntervalIntegrable
      (fun y : Real => f ((left : Complex) + y * Complex.I)) volume bottom split)
    (hleft_top : IntervalIntegrable
      (fun y : Real => f ((left : Complex) + y * Complex.I)) volume split top) :
    rectangleBoundaryIntegralCoords f left right bottom top =
      rectangleBoundaryIntegralCoords f left right bottom split := by
  unfold rectangleBoundaryIntegralCoords at hstrip ⊢
  simp only [smul_eq_mul] at hstrip ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals hright_bottom hright_top]
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft_bottom hleft_top]
  linear_combination hstrip

/-- A pole is continuous, hence interval-integrable, on a horizontal segment
that avoids it.  The segment hypothesis is intentionally local: a pole on the
same horizontal line but outside the integration interval is harmless. -/
private theorem intervalIntegrable_rectangleSimplePole_horizontal
    (u : Complex) {y left right : Real}
    (hsegment : ∀ x ∈ [[left, right]], (x : Complex) + y * Complex.I ≠ u) :
    IntervalIntegrable
      (fun x : Real => rectangleSimplePole u ((x : Complex) + y * Complex.I))
      volume left right := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hz_ne : (x : Complex) + y * Complex.I ≠ u := hsegment x hx
  have hpath : ContinuousAt (fun x : Real => (x : Complex) + y * Complex.I) x := by
    fun_prop
  have hcomp : ContinuousAt
      (rectangleSimplePole u ∘ fun x : Real => (x : Complex) + y * Complex.I) x :=
    ContinuousAt.comp (f := fun x : Real => (x : Complex) + y * Complex.I)
      (differentiableAt_rectangleSimplePole_of_ne hz_ne).continuousAt hpath
  exact hcomp.continuousWithinAt

private theorem horizontalSegment_avoids_rectangleSimplePole_of_ne_im
    (u : Complex) {y left right : Real} (hy : y ≠ u.im) :
    ∀ x ∈ [[left, right]], (x : Complex) + y * Complex.I ≠ u := by
  intro x hx hxu
  apply hy
  have him := congrArg Complex.im hxu
  simpa using him

/-- A pole is continuous, hence interval-integrable, on a vertical segment
that avoids it. -/
private theorem intervalIntegrable_rectangleSimplePole_vertical
    (u : Complex) {x bottom top : Real}
    (hsegment : ∀ y ∈ [[bottom, top]], (x : Complex) + y * Complex.I ≠ u) :
    IntervalIntegrable
      (fun y : Real => rectangleSimplePole u ((x : Complex) + y * Complex.I))
      volume bottom top := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hz_ne : (x : Complex) + y * Complex.I ≠ u := hsegment y hy
  have hpath : ContinuousAt (fun y : Real => (x : Complex) + y * Complex.I) y := by
    fun_prop
  have hcomp : ContinuousAt
      (rectangleSimplePole u ∘ fun y : Real => (x : Complex) + y * Complex.I) y :=
    ContinuousAt.comp (f := fun y : Real => (x : Complex) + y * Complex.I)
      (differentiableAt_rectangleSimplePole_of_ne hz_ne).continuousAt hpath
  exact hcomp.continuousWithinAt

private theorem verticalSegment_avoids_rectangleSimplePole_of_ne_re
    (u : Complex) {x bottom top : Real} (hx : x ≠ u.re) :
    ∀ y ∈ [[bottom, top]], (x : Complex) + y * Complex.I ≠ u := by
  intro y hy hyu
  apply hx
  have hre := congrArg Complex.re hyu
  simpa using hre

/-- A finite sum may pass through the four rectangle-edge integrals once every
summand is integrable on the corresponding edge.  The hypotheses deliberately
keep boundary-pole exclusion explicit. -/
private theorem xiRectangleBoundaryIntegral_finset_sum
    (s : Finset Complex) (f : Complex -> Complex -> Complex) (z w : Complex)
    (hbottom : ∀ u ∈ s, IntervalIntegrable
      (fun x : Real => f u ((x : Complex) + z.im * Complex.I)) volume z.re w.re)
    (htop : ∀ u ∈ s, IntervalIntegrable
      (fun x : Real => f u ((x : Complex) + w.im * Complex.I)) volume z.re w.re)
    (hright : ∀ u ∈ s, IntervalIntegrable
      (fun y : Real => f u ((w.re : Complex) + y * Complex.I)) volume z.im w.im)
    (hleft : ∀ u ∈ s, IntervalIntegrable
      (fun y : Real => f u ((z.re : Complex) + y * Complex.I)) volume z.im w.im) :
    xiRectangleBoundaryIntegral (fun q => ∑ u ∈ s, f u q) z w =
      ∑ u ∈ s, xiRectangleBoundaryIntegral (f u) z w := by
  unfold xiRectangleBoundaryIntegral
  rw [intervalIntegral.integral_finsetSum hbottom,
    intervalIntegral.integral_finsetSum htop,
    intervalIntegral.integral_finsetSum hright,
    intervalIntegral.integral_finsetSum hleft]
  simp only [smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

private theorem xiRectangleBoundaryIntegral_const_mul
    (a : Complex) (f : Complex -> Complex) (z w : Complex) :
    xiRectangleBoundaryIntegral (fun q => a * f q) z w =
      a * xiRectangleBoundaryIntegral f z w := by
  unfold xiRectangleBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

private theorem strictlyInsideRectangle_of_mem_rectangle_of_boundary_avoids
    {z w u : Complex} (hstandard : standardRectangle z w)
    (hmem : u ∈ Complex.Rectangle z w)
    (hbottom : ∀ x ∈ [[z.re, w.re]], (x : Complex) + z.im * Complex.I ≠ u)
    (htop : ∀ x ∈ [[z.re, w.re]], (x : Complex) + w.im * Complex.I ≠ u)
    (hright : ∀ y ∈ [[z.im, w.im]], (w.re : Complex) + y * Complex.I ≠ u)
    (hleft : ∀ y ∈ [[z.im, w.im]], (z.re : Complex) + y * Complex.I ≠ u) :
    strictlyInsideRectangle z w u := by
  rw [Complex.Rectangle, Complex.mem_reProdIm] at hmem
  have hmemRe : u.re ∈ Set.Icc z.re w.re := by
    simpa only [uIcc_of_le hstandard.1.le] using hmem.1
  have hmemIm : u.im ∈ Set.Icc z.im w.im := by
    simpa only [uIcc_of_le hstandard.2.le] using hmem.2
  have hleft : u.re ≠ z.re := by
    intro h
    apply hleft u.im hmem.2
    apply Complex.ext <;> simp [h]
  have hright : u.re ≠ w.re := by
    intro h
    apply hright u.im hmem.2
    apply Complex.ext <;> simp [h]
  have hbottom : u.im ≠ z.im := by
    intro h
    apply hbottom u.re hmem.1
    apply Complex.ext <;> simp [h]
  have htop : u.im ≠ w.im := by
    intro h
    apply htop u.re hmem.1
    apply Complex.ext <;> simp [h]
  exact ⟨lt_of_le_of_ne hmemRe.1 hleft.symm, lt_of_le_of_ne hmemRe.2 hright,
    lt_of_le_of_ne hmemIm.1 hbottom.symm, lt_of_le_of_ne hmemIm.2 htop⟩

private theorem rectangleBoundaryIntegralCoords_rectangleSimplePole_eq_zero_of_right_lt_re
    (u : Complex) {left right bottom top : Real} (hleft_right : left ≤ right)
    (hright : right < u.re) :
    rectangleBoundaryIntegralCoords (rectangleSimplePole u) left right bottom top = 0 := by
  rw [← xiRectangleBoundaryIntegral_eq_coords]
  apply xiRectangleBoundaryIntegral_rectangleSimplePole_eq_zero_of_not_mem_rectangle
  intro hu
  rw [mem_complexRectangle_coords_iff] at hu
  rw [uIcc_of_le hleft_right] at hu
  exact (not_le_of_gt hright) hu.1.2

private theorem rectangleBoundaryIntegralCoords_rectangleSimplePole_eq_zero_of_re_lt_left
    (u : Complex) {left right bottom top : Real} (hleft_right : left ≤ right)
    (hleft : u.re < left) :
    rectangleBoundaryIntegralCoords (rectangleSimplePole u) left right bottom top = 0 := by
  rw [← xiRectangleBoundaryIntegral_eq_coords]
  apply xiRectangleBoundaryIntegral_rectangleSimplePole_eq_zero_of_not_mem_rectangle
  intro hu
  rw [mem_complexRectangle_coords_iff] at hu
  rw [uIcc_of_le hleft_right] at hu
  exact (not_le_of_gt hleft) hu.1.1

private theorem rectangleBoundaryIntegralCoords_rectangleSimplePole_eq_zero_of_top_lt_im
    (u : Complex) {left right bottom top : Real} (hbottom_top : bottom ≤ top)
    (htop : top < u.im) :
    rectangleBoundaryIntegralCoords (rectangleSimplePole u) left right bottom top = 0 := by
  rw [← xiRectangleBoundaryIntegral_eq_coords]
  apply xiRectangleBoundaryIntegral_rectangleSimplePole_eq_zero_of_not_mem_rectangle
  intro hu
  rw [mem_complexRectangle_coords_iff] at hu
  rw [uIcc_of_le hbottom_top] at hu
  exact (not_le_of_gt htop) hu.2.2

private theorem rectangleBoundaryIntegralCoords_rectangleSimplePole_eq_zero_of_im_lt_bottom
    (u : Complex) {left right bottom top : Real} (hbottom_top : bottom ≤ top)
    (hbottom : u.im < bottom) :
    rectangleBoundaryIntegralCoords (rectangleSimplePole u) left right bottom top = 0 := by
  rw [← xiRectangleBoundaryIntegral_eq_coords]
  apply xiRectangleBoundaryIntegral_rectangleSimplePole_eq_zero_of_not_mem_rectangle
  intro hu
  rw [mem_complexRectangle_coords_iff] at hu
  rw [uIcc_of_le hbottom_top] at hu
  exact (not_le_of_gt hbottom) hu.2.1

/-- A positive-oriented rectangle containing the simple pole strictly in its
interior has the expected residue.  The proof shrinks to a centered square and
uses Cauchy-Goursat only on the four pole-free strips between the rectangles. -/
theorem xiRectangleBoundaryIntegral_rectangleSimplePole_eq_two_pi_I_of_strictlyInside
    {z w u : Complex} (hu : strictlyInsideRectangle z w u) :
    xiRectangleBoundaryIntegral (rectangleSimplePole u) z w =
      2 * (Real.pi : Complex) * Complex.I := by
  rcases hu with ⟨hzre, hrew, hzim, himw⟩
  let delta : Real := min (u.re - z.re)
    (min (w.re - u.re) (min (u.im - z.im) (w.im - u.im)))
  let radius : Real := delta / 2
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hdelta_left : delta ≤ u.re - z.re := by
    dsimp [delta]
    exact min_le_left _ _
  have hdelta_right : delta ≤ w.re - u.re := by
    dsimp [delta]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hdelta_bottom : delta ≤ u.im - z.im := by
    dsimp [delta]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdelta_top : delta ≤ w.im - u.im := by
    dsimp [delta]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hleft_inner : z.re < u.re - radius := by
    dsimp [radius]
    linarith
  have hright_inner : u.re + radius < w.re := by
    dsimp [radius]
    linarith
  have hbottom_inner : z.im < u.im - radius := by
    dsimp [radius]
    linarith
  have htop_inner : u.im + radius < w.im := by
    dsimp [radius]
    linarith
  have hleft_strip : rectangleBoundaryIntegralCoords (rectangleSimplePole u)
      z.re (u.re - radius) (u.im - radius) (u.im + radius) = 0 :=
    rectangleBoundaryIntegralCoords_rectangleSimplePole_eq_zero_of_right_lt_re u
      hleft_inner.le (by linarith)
  have hright_strip : rectangleBoundaryIntegralCoords (rectangleSimplePole u)
      (u.re + radius) w.re (u.im - radius) (u.im + radius) = 0 :=
    rectangleBoundaryIntegralCoords_rectangleSimplePole_eq_zero_of_re_lt_left u
      hright_inner.le (by linarith)
  have hbottom_strip : rectangleBoundaryIntegralCoords (rectangleSimplePole u)
      z.re w.re z.im (u.im - radius) = 0 :=
    rectangleBoundaryIntegralCoords_rectangleSimplePole_eq_zero_of_top_lt_im u
      hbottom_inner.le (by linarith)
  have htop_strip : rectangleBoundaryIntegralCoords (rectangleSimplePole u)
      z.re w.re (u.im + radius) w.im = 0 :=
    rectangleBoundaryIntegralCoords_rectangleSimplePole_eq_zero_of_im_lt_bottom u
      htop_inner.le (by linarith)
  have hbottom_ne : u.im - radius ≠ u.im := by linarith
  have htop_ne : u.im + radius ≠ u.im := by linarith
  have hleft_ne : u.re - radius ≠ u.re := by linarith
  have hright_ne : u.re + radius ≠ u.re := by linarith
  have hbottom_zl := intervalIntegrable_rectangleSimplePole_horizontal u
    (left := z.re) (right := u.re - radius)
    (horizontalSegment_avoids_rectangleSimplePole_of_ne_im u hbottom_ne)
  have hbottom_lr := intervalIntegrable_rectangleSimplePole_horizontal u
    (left := u.re - radius) (right := u.re + radius)
    (horizontalSegment_avoids_rectangleSimplePole_of_ne_im u hbottom_ne)
  have htop_zl := intervalIntegrable_rectangleSimplePole_horizontal u
    (left := z.re) (right := u.re - radius)
    (horizontalSegment_avoids_rectangleSimplePole_of_ne_im u htop_ne)
  have htop_lr := intervalIntegrable_rectangleSimplePole_horizontal u
    (left := u.re - radius) (right := u.re + radius)
    (horizontalSegment_avoids_rectangleSimplePole_of_ne_im u htop_ne)
  have hbottom_zr := intervalIntegrable_rectangleSimplePole_horizontal u
    (left := z.re) (right := u.re + radius)
    (horizontalSegment_avoids_rectangleSimplePole_of_ne_im u hbottom_ne)
  have hbottom_rw := intervalIntegrable_rectangleSimplePole_horizontal u
    (left := u.re + radius) (right := w.re)
    (horizontalSegment_avoids_rectangleSimplePole_of_ne_im u hbottom_ne)
  have htop_zr := intervalIntegrable_rectangleSimplePole_horizontal u
    (left := z.re) (right := u.re + radius)
    (horizontalSegment_avoids_rectangleSimplePole_of_ne_im u htop_ne)
  have htop_rw := intervalIntegrable_rectangleSimplePole_horizontal u
    (left := u.re + radius) (right := w.re)
    (horizontalSegment_avoids_rectangleSimplePole_of_ne_im u htop_ne)
  have hhorizontal_left := rectangleBoundaryIntegralCoords_expand_left (rectangleSimplePole u)
    hleft_strip hbottom_zl hbottom_lr htop_zl htop_lr
  have hhorizontal_right := rectangleBoundaryIntegralCoords_expand_right (rectangleSimplePole u)
    hright_strip hbottom_zr hbottom_rw htop_zr htop_rw
  have hright_bottom := intervalIntegrable_rectangleSimplePole_vertical u
    (x := w.re) (bottom := z.im) (top := u.im - radius)
    (verticalSegment_avoids_rectangleSimplePole_of_ne_re u (by linarith))
  have hright_inner := intervalIntegrable_rectangleSimplePole_vertical u
    (x := w.re) (bottom := u.im - radius) (top := u.im + radius)
    (verticalSegment_avoids_rectangleSimplePole_of_ne_re u (by linarith))
  have hleft_bottom := intervalIntegrable_rectangleSimplePole_vertical u
    (x := z.re) (bottom := z.im) (top := u.im - radius)
    (verticalSegment_avoids_rectangleSimplePole_of_ne_re u (by linarith))
  have hleft_inner := intervalIntegrable_rectangleSimplePole_vertical u
    (x := z.re) (bottom := u.im - radius) (top := u.im + radius)
    (verticalSegment_avoids_rectangleSimplePole_of_ne_re u (by linarith))
  have hright_to_inner := intervalIntegrable_rectangleSimplePole_vertical u
    (x := w.re) (bottom := z.im) (top := u.im + radius)
    (verticalSegment_avoids_rectangleSimplePole_of_ne_re u (by linarith))
  have hright_top := intervalIntegrable_rectangleSimplePole_vertical u
    (x := w.re) (bottom := u.im + radius) (top := w.im)
    (verticalSegment_avoids_rectangleSimplePole_of_ne_re u (by linarith))
  have hleft_to_inner := intervalIntegrable_rectangleSimplePole_vertical u
    (x := z.re) (bottom := z.im) (top := u.im + radius)
    (verticalSegment_avoids_rectangleSimplePole_of_ne_re u (by linarith))
  have hleft_top := intervalIntegrable_rectangleSimplePole_vertical u
    (x := z.re) (bottom := u.im + radius) (top := w.im)
    (verticalSegment_avoids_rectangleSimplePole_of_ne_re u (by linarith))
  have hvertical_bottom := rectangleBoundaryIntegralCoords_expand_bottom (rectangleSimplePole u)
    hbottom_strip hright_bottom hright_inner hleft_bottom hleft_inner
  have hvertical_top := rectangleBoundaryIntegralCoords_expand_top (rectangleSimplePole u)
    htop_strip hright_to_inner hright_top hleft_to_inner hleft_top
  have hz_coords : ((z.re : Complex) + z.im * Complex.I) = z := by
    apply Complex.ext <;> simp
  have hw_coords : ((w.re : Complex) + w.im * Complex.I) = w := by
    apply Complex.ext <;> simp
  have hboundary_coords :
      xiRectangleBoundaryIntegral (rectangleSimplePole u)
          ((z.re : Complex) + z.im * Complex.I)
          ((w.re : Complex) + w.im * Complex.I) =
        rectangleBoundaryIntegralCoords (rectangleSimplePole u) z.re w.re z.im w.im := by
    simpa using xiRectangleBoundaryIntegral_eq_coords (rectangleSimplePole u)
      z.re w.re z.im w.im
  have hcenter_coords :
      rectangleBoundaryIntegralCoords (rectangleSimplePole u)
          (u.re - radius) (u.re + radius) (u.im - radius) (u.im + radius) =
        xiRectangleBoundaryIntegral (rectangleSimplePole u)
          ((u.re - radius : Real) + (u.im - radius) * Complex.I)
          ((u.re + radius : Real) + (u.im + radius) * Complex.I) := by
    simpa using (xiRectangleBoundaryIntegral_eq_coords (rectangleSimplePole u)
      (u.re - radius) (u.re + radius) (u.im - radius) (u.im + radius)).symm
  calc
    xiRectangleBoundaryIntegral (rectangleSimplePole u) z w =
        rectangleBoundaryIntegralCoords (rectangleSimplePole u) z.re w.re z.im w.im := by
      calc
        xiRectangleBoundaryIntegral (rectangleSimplePole u) z w =
            xiRectangleBoundaryIntegral (rectangleSimplePole u)
              ((z.re : Complex) + z.im * Complex.I)
              ((w.re : Complex) + w.im * Complex.I) := by rw [hz_coords, hw_coords]
        _ = rectangleBoundaryIntegralCoords (rectangleSimplePole u) z.re w.re z.im w.im :=
          hboundary_coords
    _ = rectangleBoundaryIntegralCoords (rectangleSimplePole u)
        z.re w.re z.im (u.im + radius) := hvertical_top
    _ = rectangleBoundaryIntegralCoords (rectangleSimplePole u)
        z.re w.re (u.im - radius) (u.im + radius) := hvertical_bottom
    _ = rectangleBoundaryIntegralCoords (rectangleSimplePole u)
        (u.re - radius) (u.re + radius) (u.im - radius) (u.im + radius) := by
      calc
        rectangleBoundaryIntegralCoords (rectangleSimplePole u)
            z.re w.re (u.im - radius) (u.im + radius) =
            rectangleBoundaryIntegralCoords (rectangleSimplePole u)
              z.re (u.re + radius) (u.im - radius) (u.im + radius) := hhorizontal_right
        _ = rectangleBoundaryIntegralCoords (rectangleSimplePole u)
              (u.re - radius) (u.re + radius) (u.im - radius) (u.im + radius) :=
          hhorizontal_left
    _ = 2 * (Real.pi : Complex) * Complex.I := by
      rw [hcenter_coords]
      exact xiRectangleBoundaryIntegral_rectangleSimplePole_eq_two_pi_I_of_center hradius

/-- One summand of the finite xi principal kernel, separated from its finite
factor owner only for linearity of the four boundary integrals. -/
private noncomputable def rectanglePrincipalPole
    (F : CompactLogTest) (c : Complex) (R : Real) (u q : Complex) : Complex :=
  -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u / (q - u))

private theorem rectanglePrincipalPole_eq_const_mul_simplePole
    (F : CompactLogTest) (c : Complex) (R : Real) (u q : Complex) :
    rectanglePrincipalPole F c R u q =
      (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
        rectangleSimplePole u q := by
  unfold rectanglePrincipalPole rectangleSimplePole
  rw [div_eq_mul_inv]
  ring

private theorem xiRectangleBoundaryIntegral_rectanglePrincipalPole_eq_of_strictlyInside
    (F : CompactLogTest) (c : Complex) (R : Real) {z w u : Complex}
    (hu : strictlyInsideRectangle z w u) :
    xiRectangleBoundaryIntegral (rectanglePrincipalPole F c R u) z w =
      -(2 * (Real.pi : Complex) * Complex.I *
        ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) := by
  rw [show rectanglePrincipalPole F c R u = fun q =>
      (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
        rectangleSimplePole u q by
      funext q
      exact rectanglePrincipalPole_eq_const_mul_simplePole F c R u q]
  rw [xiRectangleBoundaryIntegral_const_mul,
    xiRectangleBoundaryIntegral_rectangleSimplePole_eq_two_pi_I_of_strictlyInside hu]
  ring

private theorem xiRectangleBoundaryIntegral_rectanglePrincipalPole_eq_zero_of_not_mem_rectangle
    (F : CompactLogTest) (c : Complex) (R : Real) {z w u : Complex}
    (hu : u ∉ Complex.Rectangle z w) :
    xiRectangleBoundaryIntegral (rectanglePrincipalPole F c R u) z w = 0 := by
  rw [show rectanglePrincipalPole F c R u = fun q =>
      (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
        rectangleSimplePole u q by
      funext q
      exact rectanglePrincipalPole_eq_const_mul_simplePole F c R u q]
  rw [xiRectangleBoundaryIntegral_const_mul,
    xiRectangleBoundaryIntegral_rectangleSimplePole_eq_zero_of_not_mem_rectangle hu,
    mul_zero]

private theorem intervalIntegrable_rectanglePrincipalPole_horizontal
    (F : CompactLogTest) (c : Complex) (R : Real) (u : Complex)
    {y left right : Real}
    (hsegment : ∀ x ∈ [[left, right]], (x : Complex) + y * Complex.I ≠ u) :
    IntervalIntegrable
      (fun x : Real => rectanglePrincipalPole F c R u ((x : Complex) + y * Complex.I))
      volume left right := by
  rw [show (fun x : Real => rectanglePrincipalPole F c R u
      ((x : Complex) + y * Complex.I)) = fun x : Real =>
        (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
          rectangleSimplePole u ((x : Complex) + y * Complex.I) by
      funext x
      exact rectanglePrincipalPole_eq_const_mul_simplePole F c R u _]
  exact (intervalIntegrable_rectangleSimplePole_horizontal u hsegment).const_mul _

private theorem intervalIntegrable_rectanglePrincipalPole_vertical
    (F : CompactLogTest) (c : Complex) (R : Real) (u : Complex)
    {x bottom top : Real}
    (hsegment : ∀ y ∈ [[bottom, top]], (x : Complex) + y * Complex.I ≠ u) :
    IntervalIntegrable
      (fun y : Real => rectanglePrincipalPole F c R u ((x : Complex) + y * Complex.I))
      volume bottom top := by
  rw [show (fun y : Real => rectanglePrincipalPole F c R u
      ((x : Complex) + y * Complex.I)) = fun y : Real =>
        (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
          rectangleSimplePole u ((x : Complex) + y * Complex.I) by
      funext y
      exact rectanglePrincipalPole_eq_const_mul_simplePole F c R u _]
  exact (intervalIntegrable_rectangleSimplePole_vertical u hsegment).const_mul _

/-- A zero-free xi rectangle boundary excludes every support point of the same
finite xi divisor from that boundary.  The divisor-to-xi bridge supplies the
only direction used here; no total value of `logDeriv` is read at a zero. -/
theorem rectangleBoundaryAvoidsFiniteSupport_of_xiRectangleBoundaryAvoidsZeros
    (c : Complex) (R : Real) {z w : Complex}
    (hboundary : xiRectangleBoundaryAvoidsZeros z w) :
    rectangleBoundaryAvoidsFiniteSupport c R z w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu x hx hxu
    have hzero := (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support c R
      ((xiClosedBallDivisor_support_finite c R).mem_toFinset.mp hu)).2
    apply hboundary.1 x hx
    rw [hxu]
    exact hzero
  · intro u hu x hx hxu
    have hzero := (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support c R
      ((xiClosedBallDivisor_support_finite c R).mem_toFinset.mp hu)).2
    apply hboundary.2.1 x hx
    rw [hxu]
    exact hzero
  · intro u hu y hy hyu
    have hzero := (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support c R
      ((xiClosedBallDivisor_support_finite c R).mem_toFinset.mp hu)).2
    apply hboundary.2.2.1 y hy
    rw [hyu]
    exact hzero
  · intro u hu y hy hyu
    have hzero := (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support c R
      ((xiClosedBallDivisor_support_finite c R).mem_toFinset.mp hu)).2
    apply hboundary.2.2.2 y hy
    rw [hyu]
    exact hzero

/-- The finite principal part of one closed-ball xi factor reads on a standard
rectangle as the sum of exactly the factor-owned divisor points strictly inside
that rectangle.  The caller supplies support-boundary avoidance, so no term is
evaluated on a pole and every non-interior support point is provably exterior. -/
theorem xiRectangleBoundaryIntegral_xiClosedBallPrincipalKernel_eq_sum_of_strictlyInside
    (F : CompactLogTest) {c : Complex} {R : Real} {z w : Complex}
    (hstandard : standardRectangle z w)
    (hboundary : rectangleBoundaryAvoidsFiniteSupport c R z w) :
    xiRectangleBoundaryIntegral (xiClosedBallPrincipalKernel F c R) z w =
      ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        @ite (α := Complex) (strictlyInsideRectangle z w u) (Classical.propDecidable _)
          (-(2 * (Real.pi : Complex) * Complex.I *
            ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u))) 0 := by
  rcases hboundary with ⟨hboundaryBottom, hboundaryTop, hboundaryRight, hboundaryLeft⟩
  classical
  letI : DecidablePred (strictlyInsideRectangle z w) := Classical.decPred _
  let support : Finset Complex := (xiClosedBallDivisor_support_finite c R).toFinset
  have hbottom : ∀ u ∈ support, IntervalIntegrable
      (fun x : Real => rectanglePrincipalPole F c R u
        ((x : Complex) + z.im * Complex.I)) volume z.re w.re := by
    intro u hu
    exact intervalIntegrable_rectanglePrincipalPole_horizontal F c R u
      (hboundaryBottom u hu)
  have htop : ∀ u ∈ support, IntervalIntegrable
      (fun x : Real => rectanglePrincipalPole F c R u
        ((x : Complex) + w.im * Complex.I)) volume z.re w.re := by
    intro u hu
    exact intervalIntegrable_rectanglePrincipalPole_horizontal F c R u
      (hboundaryTop u hu)
  have hright : ∀ u ∈ support, IntervalIntegrable
      (fun y : Real => rectanglePrincipalPole F c R u
        ((w.re : Complex) + y * Complex.I)) volume z.im w.im := by
    intro u hu
    exact intervalIntegrable_rectanglePrincipalPole_vertical F c R u
      (hboundaryRight u hu)
  have hleft : ∀ u ∈ support, IntervalIntegrable
      (fun y : Real => rectanglePrincipalPole F c R u
        ((z.re : Complex) + y * Complex.I)) volume z.im w.im := by
    intro u hu
    exact intervalIntegrable_rectanglePrincipalPole_vertical F c R u
      (hboundaryLeft u hu)
  have hsum := xiRectangleBoundaryIntegral_finset_sum support
    (rectanglePrincipalPole F c R) z w hbottom htop hright hleft
  have hkernel : xiClosedBallPrincipalKernel F c R = fun q =>
      ∑ u ∈ support, rectanglePrincipalPole F c R u q := by
    funext q
    simp only [xiClosedBallPrincipalKernel, rectanglePrincipalPole, support]
  rw [hkernel, hsum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huinside : strictlyInsideRectangle z w u
  · rw [if_pos huinside]
    exact xiRectangleBoundaryIntegral_rectanglePrincipalPole_eq_of_strictlyInside F c R huinside
  · rw [if_neg huinside]
    apply xiRectangleBoundaryIntegral_rectanglePrincipalPole_eq_zero_of_not_mem_rectangle
    intro humem
    have hstrict := strictlyInsideRectangle_of_mem_rectangle_of_boundary_avoids hstandard humem
      (hboundaryBottom u hu) (hboundaryTop u hu) (hboundaryRight u hu) (hboundaryLeft u hu)
    exact huinside hstrict

/-- The complete xi contour kernel reads on a standard zero-free rectangle as
the finite principal-pole sum of one factor owner.  Cauchy-Goursat eliminates
only the differentiable regularized remainder; the residues are supplied by
the finite support readout above. -/
theorem xiRectangleBoundaryIntegral_xiContourKernel_eq_sum_of_strictlyInside
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ q : Metric.closedBall c |R|, g q ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z w : Complex} (hrectangle : Complex.Rectangle z w ⊆ Metric.ball c |R|)
    (hstandard : standardRectangle z w)
    (hboundary : xiRectangleBoundaryAvoidsZeros z w) :
    xiRectangleBoundaryIntegral (xiContourKernel F) z w =
      ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        @ite (α := Complex) (strictlyInsideRectangle z w u) (Classical.propDecidable _)
          (-(2 * (Real.pi : Complex) * Complex.I *
            ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u))) 0 := by
  rw [xiRectangleBoundaryIntegral_xiContourKernel_eq_principal F hanalytic hnonzero hfactor
    hrectangle hboundary]
  exact xiRectangleBoundaryIntegral_xiClosedBallPrincipalKernel_eq_sum_of_strictlyInside F
    hstandard (rectangleBoundaryAvoidsFiniteSupport_of_xiRectangleBoundaryAvoidsZeros c R hboundary)

end C1XiFiniteRectanglePrincipalPart
end Source
end ConnesWeilRH
