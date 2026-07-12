/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaConvolution

/-!
# Full-product finite interpolation for the Yoshida assembly

The correction factor must interpolate values after division by the rescaled
base power. Interpolating the correction to one does not normalize the
assembled convolution product.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20YoshidaConvolution

open MeasureTheory
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped ComplexConjugate

namespace CompactLogTest

/-- The reciprocal rescaling used by the support-preserving base power. -/
noncomputable def fullProductScale (n : ℕ) : ℂ :=
  Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹)

/-- The rescaled base factor appearing in the support-preserving convolution
assembly. -/
noncomputable def fullProductBaseFactor
    (f : CompactLogTest) (n : ℕ) (s : ℂ) : ℂ :=
  laplaceAt f (fullProductScale n * s)

/-- Nodes at which a base test must be normalized in order for the assembled
base factor to be one at the original nodes. -/
noncomputable def fullProductScaledNodes (n : ℕ) (nodes : Finset ℂ) :
    Finset ℂ :=
  nodes.image fun z => fullProductScale n * z

/-- Close a finite node set under the involution which occurs in the Laplace
transform of a convolution square. -/
noncomputable def hermitianNodeClosure (nodes : Finset ℂ) : Finset ℂ :=
  nodes ∪ nodes.image fun z => -star z

/-- The Laplace transform of the additive involution. This is the identity
that makes a convolution square an actual positive-definite base rather than
an arbitrary finite-node interpolant. -/
theorem laplaceAt_involution (f : CompactLogTest) (s : ℂ) :
    laplaceAt f.involution s = star (laplaceAt f (-star s)) := by
  unfold laplaceAt
  simp only [exponentialWeight_apply, CompactLogTest.involution_apply]
  let reflected : ℝ → ℂ := fun x =>
    Complex.exp ((-s) * (x : ℂ)) * star (f.test x)
  have hrewrite :
      (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * star (f.test (-x))) =
        fun x => reflected (-x) := by
    funext x
    dsimp [reflected]
    congr 2
    push_cast
    ring
  rw [hrewrite, integral_neg_eq_self]
  change (∫ x : ℝ, reflected x) = conj
    (∫ x : ℝ, Complex.exp ((-star s) * (x : ℂ)) * f.test x)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [reflected]
  change Complex.exp ((-s) * (x : ℂ)) * star (f.test x) =
    (starRingEnd ℂ) (Complex.exp ((-star s) * (x : ℂ)) * f.test x)
  rw [map_mul]
  rw [← Complex.exp_conj]
  congr 2
  simp

/-- A convolution square is supported in the symmetric difference window of
its factor. -/
theorem convolutionSquare_support_subset_symmetric
    (f : CompactLogTest) {a : ℝ}
    (hsupport : Function.support f.test ⊆ Set.Ioo (-a / 2) (a / 2)) :
    Function.support f.convolutionSquare.test ⊆ Set.Ioo (-a) a := by
  have hsquare := CCM25Concrete.SelectedYoshidaBridge.convolutionSquare_support_subset_difference
    f hsupport
  rw [show -a / 2 - a / 2 = -a by ring,
    show a / 2 - -a / 2 = a by ring] at hsquare
  exact hsquare

/-- The full-product base factor of a convolution square is the paired
Hermitian Laplace product. -/
theorem fullProductBaseFactor_convolutionSquare
    (h : CompactLogTest) (n : ℕ) (s : ℂ) :
    fullProductBaseFactor h.convolutionSquare n s =
      star (laplaceAt h (-star (fullProductScale n * s))) *
        laplaceAt h (fullProductScale n * s) := by
  unfold fullProductBaseFactor
  rw [CompactLogTest.convolutionSquare, laplaceAt_convolution,
    laplaceAt_involution]

/-- A positive-real-part target cannot collide with the Hermitian companion of
a nonnegative-real-part node after the positive support-preserving rescaling. -/
theorem fullProductScale_mul_ne_neg_star_of_re_nonneg_pos
    (n : ℕ) (z rho : ℂ) (hz : 0 ≤ z.re) (hrho : 0 < rho.re) :
    fullProductScale n * z ≠ -star (fullProductScale n * rho) := by
  intro hEq
  have hre := congrArg Complex.re hEq
  simp [fullProductScale] at hre
  have hnumerator : 0 < (n : ℝ) + 1 := by positivity
  have hne : (n : ℂ) + 1 ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    simp at hreal
    linarith
  have hdenominator : 0 < Complex.normSq ((n : ℂ) + 1) :=
    Complex.normSq_pos.mpr hne
  have hcoeff : 0 < (((n : ℝ) + 1) /
      Complex.normSq ((n : ℂ) + 1)) := div_pos hnumerator hdenominator
  nlinarith [hcoeff]

theorem laplaceAt_convolutionIterate_rescale_inv_natCast_convolution_eq_fullProduct
    (f correction : CompactLogTest) (s : ℂ) (n : ℕ) :
    laplaceAt
        ((convolutionIterate
          (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
            correction) s =
      (fullProductBaseFactor f n s) ^ (n + 1) * laplaceAt correction s := by
  simpa only [fullProductBaseFactor, fullProductScale] using
    laplaceAt_convolutionIterate_rescale_inv_natCast_convolution f correction s n

/-- The support-preserving convolution power of a convolution square is again
a convolution square.  The factor is the corresponding power of the original
factor, so positivity is retained by construction rather than inferred from a
transform identity. -/
theorem laplaceAt_convolutionSquare_convolutionIterate_rescale_inv_natCast
    (h : CompactLogTest) (s : ℂ) (n : ℕ) :
    laplaceAt
        (convolutionIterate
          (rescale h (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolutionSquare s =
      (fullProductBaseFactor h.convolutionSquare n s) ^ (n + 1) := by
  rw [CompactLogTest.convolutionSquare, laplaceAt_convolution,
    laplaceAt_involution, laplaceAt_convolutionIterate,
    laplaceAt_convolutionIterate, laplaceAt_rescale, laplaceAt_rescale,
    fullProductBaseFactor_convolutionSquare]
  rw [star_pow, mul_pow]
  congr 3 <;> push_cast <;> simp [fullProductScale] <;> ring

/-- A compact base can be normalized to make every full-product base factor
equal one on a finite node set. The construction also retains a uniform
quadratic strip bound. It does not assert positivity of the base test. -/
theorem exists_residualWindow_base_fullProduct_normalized_with_quadratic_decay
    (n : ℕ) (nodes : Finset ℂ) {lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ f : CompactLogTest, ∃ C : ℝ,
      Function.support f.test ⊆ Set.Ioo lower upper ∧
        (∀ z : FiniteMellinNode nodes,
          fullProductBaseFactor f n z.1 = 1) ∧
        0 ≤ C ∧
          ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
            ‖t / (2 * Real.pi)‖ ^ 2 *
                ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨f, C, hsupport, hvalues, hC, hdecay⟩ :=
    exists_residualWindow_correction_with_quadratic_decay
      (fullProductScaledNodes n nodes) hlower hupper (fun _ => 1)
  refine ⟨f, C, hsupport, ?_, hC, hdecay⟩
  intro z
  let scaledNode : FiniteMellinNode (fullProductScaledNodes n nodes) :=
    ⟨fullProductScale n * z.1,
      Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩⟩
  change laplaceAt f scaledNode.1 = 1
  simpa [scaledNode] using hvalues scaledNode

/-- A positive-definite base with no finite-node obstruction.

The base is explicitly the convolution square `h* * h`, not a stored
positivity assumption.  Interpolating `h` on the Hermitian closure of the
rescaled nodes makes the complete base factor equal one at every requested
node.  The theorem deliberately retains the decay constant for `h`; deriving
the compatible global contraction for the square is a separate tail gate. -/
theorem exists_convolutionSquare_base_fullProduct_normalized
    (n : ℕ) (nodes : Finset ℂ) {a : ℝ} (ha : 0 < a) :
    ∃ h : CompactLogTest, ∃ C : ℝ,
      Function.support h.test ⊆ Set.Ioo (-a / 2) (a / 2) ∧
      Function.support h.convolutionSquare.test ⊆ Set.Ioo (-a) a ∧
      (∀ z : FiniteMellinNode nodes,
        fullProductBaseFactor h.convolutionSquare n z.1 = 1) ∧
      0 ≤ C ∧
        ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
          ‖t / (2 * Real.pi)‖ ^ 2 *
              ‖laplaceAt h ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  let scaledNodes := fullProductScaledNodes n nodes
  obtain ⟨h, C, hsupport, hvalues, hC, hdecay⟩ :=
    exists_residualWindow_correction_with_quadratic_decay
      (hermitianNodeClosure scaledNodes)
      (by linarith : -a / 2 < 0) (by linarith : 0 < a / 2)
      (fun _ => 1)
  refine ⟨h, C, hsupport, convolutionSquare_support_subset_symmetric h hsupport,
    ?_, hC, hdecay⟩
  intro z
  let w : ℂ := fullProductScale n * z.1
  have hw_scaled : w ∈ scaledNodes := by
    exact Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩
  have hw : w ∈ hermitianNodeClosure scaledNodes :=
    Finset.mem_union_left _ hw_scaled
  have hstarw : -star w ∈ hermitianNodeClosure scaledNodes := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨w, hw_scaled, rfl⟩
  have hvalue_w : laplaceAt h w = 1 :=
    hvalues ⟨w, hw⟩
  have hvalue_starw : laplaceAt h (-star w) = 1 :=
    hvalues ⟨-star w, hstarw⟩
  change fullProductBaseFactor h.convolutionSquare n z.1 = 1
  rw [fullProductBaseFactor_convolutionSquare, hvalue_starw, hvalue_w]
  norm_num

/-- A finite detector can be made positive-definite before any tail estimate:
the target node has full-product value one and every separated node has value
zero. The explicit separation hypothesis prevents a source node from colliding
with the Hermitian companion forced by the convolution square. -/
theorem exists_convolutionSquare_base_fullProduct_indicator
    (n : ℕ) (nodes : Finset ℂ) (rho : ℂ) (hrho : rho ∈ nodes)
    (hseparate : ∀ z : FiniteMellinNode nodes, z.1 ≠ rho →
      fullProductScale n * z.1 ≠ -star (fullProductScale n * rho))
    {a : ℝ} (ha : 0 < a) :
    ∃ h : CompactLogTest, ∃ C : ℝ,
      Function.support h.test ⊆ Set.Ioo (-a / 2) (a / 2) ∧
      Function.support h.convolutionSquare.test ⊆ Set.Ioo (-a) a ∧
      fullProductBaseFactor h.convolutionSquare n rho = 1 ∧
      (∀ z : FiniteMellinNode nodes, z.1 ≠ rho →
        fullProductBaseFactor h.convolutionSquare n z.1 = 0) ∧
      0 ≤ C ∧
        ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
          ‖t / (2 * Real.pi)‖ ^ 2 *
              ‖laplaceAt h ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  let scaledNodes := fullProductScaledNodes n nodes
  let wRho : ℂ := fullProductScale n * rho
  obtain ⟨h, C, hsupport, hvalues, hC, hdecay⟩ :=
    exists_residualWindow_correction_with_quadratic_decay
      (hermitianNodeClosure scaledNodes)
      (by linarith : -a / 2 < 0) (by linarith : 0 < a / 2)
      (fun w => if w.1 = wRho ∨ w.1 = -star wRho then 1 else 0)
  refine ⟨h, C, hsupport, convolutionSquare_support_subset_symmetric h hsupport,
    ?_, ?_, hC, hdecay⟩
  · have hwRho_scaled : wRho ∈ scaledNodes := by
      exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩
    have hwRho : wRho ∈ hermitianNodeClosure scaledNodes :=
      Finset.mem_union_left _ hwRho_scaled
    have hstarRho : -star wRho ∈ hermitianNodeClosure scaledNodes := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨wRho, hwRho_scaled, rfl⟩
    have hvalue_rho : laplaceAt h wRho = 1 := by
      simpa using hvalues ⟨wRho, hwRho⟩
    have hvalue_starRho : laplaceAt h (-star wRho) = 1 := by
      simpa using hvalues ⟨-star wRho, hstarRho⟩
    change fullProductBaseFactor h.convolutionSquare n rho = 1
    rw [fullProductBaseFactor_convolutionSquare, hvalue_starRho, hvalue_rho]
    norm_num
  · intro z hzne
    let w : ℂ := fullProductScale n * z.1
    have hw_scaled : w ∈ scaledNodes := by
      exact Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩
    have hw : w ∈ hermitianNodeClosure scaledNodes :=
      Finset.mem_union_left _ hw_scaled
    have hscale : fullProductScale n ≠ 0 := by
      unfold fullProductScale
      apply Complex.ofReal_ne_zero.mpr
      exact inv_ne_zero (by positivity)
    have hw_ne_rho : w ≠ wRho := by
      intro hEq
      apply hzne
      apply mul_left_cancel₀ hscale
      simpa [w, wRho] using hEq
    have hw_ne_starRho : w ≠ -star wRho := by
      simpa [w, wRho] using hseparate z hzne
    have hvalue_zero : laplaceAt h w = 0 := by
      calc
        laplaceAt h w = if w = wRho ∨ w = -star wRho then 1 else 0 :=
          hvalues ⟨w, hw⟩
        _ = 0 := if_neg fun hEq => hEq.elim hw_ne_rho hw_ne_starRho
    change fullProductBaseFactor h.convolutionSquare n z.1 = 0
    rw [fullProductBaseFactor_convolutionSquare, hvalue_zero]
    simp

/-- Source-ready finite detector interface. The only geometric facts required
are that every node lies in the closed right half-plane and that the marked
node lies in its interior. -/
theorem exists_convolutionSquare_base_fullProduct_indicator_of_re_nonnegative
    (n : ℕ) (nodes : Finset ℂ) (rho : ℂ) (hrho_mem : rho ∈ nodes)
    (hnodes : ∀ z : FiniteMellinNode nodes, 0 ≤ z.1.re)
    (hrho : 0 < rho.re) {a : ℝ} (ha : 0 < a) :
    ∃ h : CompactLogTest, ∃ C : ℝ,
      Function.support h.test ⊆ Set.Ioo (-a / 2) (a / 2) ∧
      Function.support h.convolutionSquare.test ⊆ Set.Ioo (-a) a ∧
      fullProductBaseFactor h.convolutionSquare n rho = 1 ∧
      (∀ z : FiniteMellinNode nodes, z.1 ≠ rho →
        fullProductBaseFactor h.convolutionSquare n z.1 = 0) ∧
      0 ≤ C ∧
        ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
          ‖t / (2 * Real.pi)‖ ^ 2 *
              ‖laplaceAt h ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  apply exists_convolutionSquare_base_fullProduct_indicator n nodes rho hrho_mem
  · intro z _
    exact fullProductScale_mul_ne_neg_star_of_re_nonneg_pos n z.1 rho
      (hnodes z) hrho
  · exact ha

/-- The source-zero finite neighborhood can be joined to any right-half-plane
route-node set before constructing the positive-definite finite detector. -/
theorem exists_sourceZero_nearby_convolutionSquare_indicator
    (n : ℕ) (rho : ℂ) (R : ℝ) (routeNodes : Finset ℂ)
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) (hR : 0 ≤ R)
    (hroute : ∀ z : FiniteMellinNode routeNodes, 0 ≤ z.1.re)
    {a : ℝ} (ha : 0 < a) :
    ∃ h : CompactLogTest, ∃ C : ℝ,
      Function.support h.test ⊆ Set.Ioo (-a / 2) (a / 2) ∧
      Function.support h.convolutionSquare.test ⊆ Set.Ioo (-a) a ∧
      fullProductBaseFactor h.convolutionSquare n rho = 1 ∧
      (∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
          z.1 ≠ rho → fullProductBaseFactor h.convolutionSquare n z.1 = 0) ∧
      0 ≤ C ∧
        ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
          ‖t / (2 * Real.pi)‖ ^ 2 *
              ‖laplaceAt h ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  apply exists_convolutionSquare_base_fullProduct_indicator_of_re_nonnegative
    n (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes) rho
  · apply Finset.mem_union_left
    rw [mem_sourceNontrivialZerosInClosedBallFinset]
    exact ⟨Metric.mem_closedBall_self hR, hrho⟩
  · intro z
    rcases Finset.mem_union.mp z.2 with hzero | hrouteNode
    · exact le_of_lt
        (sourceNontrivialZero_zero_lt_re
          (mem_sourceNontrivialZerosInClosedBallFinset.mp hzero).2)
    · exact hroute ⟨z.1, hrouteNode⟩
  · exact sourceNontrivialZero_zero_lt_re hrho
  · exact ha

/-- Finite-node interpolation for the complete assembled product.

This theorem is deliberately conditional on nonvanishing of the rescaled base
factor at every prescribed node. It removes the false inference from
`laplaceAt correction rho = 1` to product-level detection, without asserting
that the needed base nonvanishing or all-zero tail estimate has been proved. -/
theorem exists_residualWindow_correction_full_product_interpolation
    (f : CompactLogTest) (n : ℕ) (nodes : Finset ℂ)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → ℂ)
    (hbase : ∀ z : FiniteMellinNode nodes,
      fullProductBaseFactor f n z.1 ≠ 0) :
    ∃ correction : CompactLogTest,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
        ∀ z : FiniteMellinNode nodes,
          laplaceAt
              ((convolutionIterate
                (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
                  correction) z.1 = y z := by
  let correctionValues : FiniteMellinNode nodes → ℂ :=
    fun z => y z / (fullProductBaseFactor f n z.1) ^ (n + 1)
  obtain ⟨correction, hsupport, hcorrection⟩ :=
    exists_residualWindow_correction nodes hlower hupper correctionValues
  refine ⟨correction, hsupport, ?_⟩
  intro z
  rw [laplaceAt_convolutionIterate_rescale_inv_natCast_convolution_eq_fullProduct,
    hcorrection]
  dsimp [correctionValues]
  exact mul_div_cancel₀ _ (pow_ne_zero _ (hbase z))

end CompactLogTest
end CC20YoshidaConvolution
end Source
end ConnesWeilRH
