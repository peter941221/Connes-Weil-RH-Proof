import ConnesWeilRH.Dev.C1XiFiniteRegularizationCauchy

/-!
# C1XiFiniteRectangleBoundary - finite xi rectangle boundary readout

The local finite-factor decomposition of the xi contour kernel is valid at
every nonzero point of a rectangle boundary.  This module packages the four
oriented interval integrals into one boundary functional, then replaces the
meromorphic xi kernel by its finite principal part on that boundary.  Cauchy
is applied only to the regularized remainder on the full rectangle.

No rectangle limit, arithmetic-side readback, explicit-formula equality, or
RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteRectangleBoundary

open Filter
open MeasureTheory
open Set
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1XiFiniteFactor
open C1XiFiniteRegularization
open C1XiFiniteRegularizationCauchy
open C1XiResidue
open C1XiVerticalFunctional
open scoped BigOperators Interval Topology

/-- The positively oriented boundary integral of an axis-parallel rectangle.
The spelling exactly matches Mathlib's rectangle Cauchy-Goursat theorem. -/
noncomputable def xiRectangleBoundaryIntegral
    (f : Complex -> Complex) (z w : Complex) : Complex :=
  (∫ x : Real in z.re..w.re, f (x + z.im * Complex.I)) -
    (∫ x : Real in z.re..w.re, f (x + w.im * Complex.I)) +
    Complex.I • (∫ y : Real in z.im..w.im, f (w.re + y * Complex.I)) -
    Complex.I • (∫ y : Real in z.im..w.im, f (z.re + y * Complex.I))

/-- The four edges of a rectangle avoid xi zeros.  This condition concerns
only the integration path; the finite principal part accounts for zeros in
the rectangle interior. -/
def xiRectangleBoundaryAvoidsZeros (z w : Complex) : Prop :=
  (∀ x ∈ [[z.re, w.re]], completedRiemannXi (x + z.im * Complex.I) ≠ 0) ∧
  (∀ x ∈ [[z.re, w.re]], completedRiemannXi (x + w.im * Complex.I) ≠ 0) ∧
  (∀ y ∈ [[z.im, w.im]], completedRiemannXi (w.re + y * Complex.I) ≠ 0) ∧
  ∀ y ∈ [[z.im, w.im]], completedRiemannXi (z.re + y * Complex.I) ≠ 0

/-- The regularized finite-factor kernel has zero rectangle boundary integral
whenever the closed rectangle belongs to its open factorization ball. -/
theorem xiRectangleBoundaryIntegral_regularized_eq_zero_of_rectangle_subset_xiBall
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    {z w : Complex}
    (hrectangle : Complex.Rectangle z w ⊆ Metric.ball c |R|) :
    xiRectangleBoundaryIntegral (xiClosedBallRegularizedKernel F c R g) z w = 0 := by
  unfold xiRectangleBoundaryIntegral
  exact integral_boundary_rect_eq_zero_of_rectangle_subset_xiBall
    F hanalytic hnonzero hrectangle

/-- Along one rectangle edge, the xi integral is the finite-principal-part
integral plus the regularized integral.  The edge lies in the same rectangle
owner, so the outer factorization-ball inclusion and the boundary nonzero
condition are used at the same point. -/
private theorem intervalIntegral_xiContourKernel_eq_principal_add_regularized_of_edge
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z w : Complex} (hrectangle : Complex.Rectangle z w ⊆ Metric.ball c |R|)
    {a b : Real} (edge : Real -> Complex)
    (hedge_continuous : Continuous edge)
    (hedge : ∀ x ∈ [[a, b]], edge x ∈ Complex.Rectangle z w)
    (hboundary : ∀ x ∈ [[a, b]], completedRiemannXi (edge x) ≠ 0) :
    (∫ x : Real in a..b, xiContourKernel F (edge x)) =
      (∫ x : Real in a..b, xiClosedBallPrincipalKernel F c R (edge x)) +
        ∫ x : Real in a..b, xiClosedBallRegularizedKernel F c R g (edge x) := by
  have hxi_continuous : ContinuousOn (fun x : Real => xiContourKernel F (edge x)) [[a, b]] := by
    intro x hx
    simpa only [Function.comp_apply] using
      (differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero F
        (hboundary x hx)).continuousAt.comp_continuousWithinAt
          hedge_continuous.continuousAt.continuousWithinAt
  have hxi_integrable :
      IntervalIntegrable (fun x : Real => xiContourKernel F (edge x)) volume a b :=
    hxi_continuous.intervalIntegrable
  have hregular_continuous : ContinuousOn
      (fun x : Real => xiClosedBallRegularizedKernel F c R g (edge x)) [[a, b]] := by
    intro x hx
    simpa only [Function.comp_apply] using
      (differentiableAt_xiClosedBallRegularizedKernel F hanalytic hnonzero
        (hrectangle (hedge x hx))).continuousAt.comp_continuousWithinAt
          hedge_continuous.continuousAt.continuousWithinAt
  have hregular_integrable : IntervalIntegrable
      (fun x : Real => xiClosedBallRegularizedKernel F c R g (edge x)) volume a b :=
    hregular_continuous.intervalIntegrable
  have hprincipal_eq : Set.EqOn
      (fun x : Real => xiClosedBallPrincipalKernel F c R (edge x))
       (fun x : Real => xiContourKernel F (edge x) -
         xiClosedBallRegularizedKernel F c R g (edge x)) [[a, b]] := by
    intro x hx
    change xiClosedBallPrincipalKernel F c R (edge x) =
      xiContourKernel F (edge x) - xiClosedBallRegularizedKernel F c R g (edge x)
    rw [xiContourKernel_eq_principal_add_regularized F hanalytic hnonzero hfactor
      (hrectangle (hedge x hx)) (hboundary x hx)]
    ring
  have hprincipal_integral :
      (∫ x : Real in a..b, xiClosedBallPrincipalKernel F c R (edge x)) =
        ∫ x : Real in a..b, xiContourKernel F (edge x) -
          xiClosedBallRegularizedKernel F c R g (edge x) :=
    intervalIntegral.integral_congr hprincipal_eq
  have hsub :
      (∫ x : Real in a..b, xiContourKernel F (edge x) -
          xiClosedBallRegularizedKernel F c R g (edge x)) =
        (∫ x : Real in a..b, xiContourKernel F (edge x)) -
          ∫ x : Real in a..b, xiClosedBallRegularizedKernel F c R g (edge x) :=
    intervalIntegral.integral_sub hxi_integrable hregular_integrable
  calc
    (∫ x : Real in a..b, xiContourKernel F (edge x)) =
        (∫ x : Real in a..b, xiContourKernel F (edge x) -
          xiClosedBallRegularizedKernel F c R g (edge x)) +
          ∫ x : Real in a..b, xiClosedBallRegularizedKernel F c R g (edge x) := by
      rw [hsub]
      ring
    _ = (∫ x : Real in a..b, xiClosedBallPrincipalKernel F c R (edge x)) +
          ∫ x : Real in a..b, xiClosedBallRegularizedKernel F c R g (edge x) := by
      rw [← hprincipal_integral]

/-- On a zero-free rectangle boundary inside one finite xi factorization ball,
the meromorphic xi contour kernel and its finite principal part have the same
boundary integral.  Interior xi zeros are retained in the principal part;
only the differentiable remainder is eliminated by rectangle Cauchy. -/
theorem xiRectangleBoundaryIntegral_xiContourKernel_eq_principal
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z w : Complex}
    (hrectangle : Complex.Rectangle z w ⊆ Metric.ball c |R|)
    (hboundary : xiRectangleBoundaryAvoidsZeros z w) :
    xiRectangleBoundaryIntegral (xiContourKernel F) z w =
      xiRectangleBoundaryIntegral (xiClosedBallPrincipalKernel F c R) z w := by
  have hbottom := intervalIntegral_xiContourKernel_eq_principal_add_regularized_of_edge
    F hanalytic hnonzero hfactor hrectangle
    (a := z.re) (b := w.re) (fun x => x + z.im * Complex.I)
    (by fun_prop)
    (by
      intro x hx
      change ((x : Complex) + (z.im : Complex) * Complex.I).re ∈ [[z.re, w.re]] ∧
        ((x : Complex) + (z.im : Complex) * Complex.I).im ∈ [[z.im, w.im]]
      have him : z.im ∈ [[z.im, w.im]] := Set.left_mem_uIcc
      exact ⟨by simp [hx], by simp [him]⟩)
    hboundary.1
  have htop := intervalIntegral_xiContourKernel_eq_principal_add_regularized_of_edge
    F hanalytic hnonzero hfactor hrectangle
    (a := z.re) (b := w.re) (fun x => x + w.im * Complex.I)
    (by fun_prop)
    (by
      intro x hx
      change ((x : Complex) + (w.im : Complex) * Complex.I).re ∈ [[z.re, w.re]] ∧
        ((x : Complex) + (w.im : Complex) * Complex.I).im ∈ [[z.im, w.im]]
      have him : w.im ∈ [[z.im, w.im]] := Set.right_mem_uIcc
      exact ⟨by simp [hx], by simp [him]⟩)
    hboundary.2.1
  have hright := intervalIntegral_xiContourKernel_eq_principal_add_regularized_of_edge
    F hanalytic hnonzero hfactor hrectangle
    (a := z.im) (b := w.im) (fun y => w.re + y * Complex.I)
    (by fun_prop)
    (by
      intro y hy
      change ((w.re : Complex) + (y : Complex) * Complex.I).re ∈ [[z.re, w.re]] ∧
        ((w.re : Complex) + (y : Complex) * Complex.I).im ∈ [[z.im, w.im]]
      have hre : w.re ∈ [[z.re, w.re]] := Set.right_mem_uIcc
      exact ⟨by simp [hre], by simp [hy]⟩)
    hboundary.2.2.1
  have hleft := intervalIntegral_xiContourKernel_eq_principal_add_regularized_of_edge
    F hanalytic hnonzero hfactor hrectangle
    (a := z.im) (b := w.im) (fun y => z.re + y * Complex.I)
    (by fun_prop)
    (by
      intro y hy
      change ((z.re : Complex) + (y : Complex) * Complex.I).re ∈ [[z.re, w.re]] ∧
        ((z.re : Complex) + (y : Complex) * Complex.I).im ∈ [[z.im, w.im]]
      have hre : z.re ∈ [[z.re, w.re]] := Set.left_mem_uIcc
      exact ⟨by simp [hre], by simp [hy]⟩)
    hboundary.2.2.2
  have hregular := xiRectangleBoundaryIntegral_regularized_eq_zero_of_rectangle_subset_xiBall
    F hanalytic hnonzero hrectangle
  unfold xiRectangleBoundaryIntegral at hregular ⊢
  rw [hbottom, htop, hright, hleft]
  simp only [smul_eq_mul] at hregular ⊢
  linear_combination hregular

end C1XiFiniteRectangleBoundary
end Source
end ConnesWeilRH
