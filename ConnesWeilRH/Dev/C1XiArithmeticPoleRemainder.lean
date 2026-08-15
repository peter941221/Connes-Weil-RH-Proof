import ConnesWeilRH.Dev.C1XiArithmeticPoleBoundary
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# C1XiArithmeticPoleRemainder - producer for the weighted pole remainder

The elementary pole contract is made concrete here.  The only singular factor
is `1 / ((c - 1) + t * I)`.  The symmetric Laplace weight is Lipschitz in the
vertical parameter on a compact rectangle, so subtracting its value at `t=0`
gives a factor `|t|`.  This cancels the Cauchy-kernel singularity uniformly and
permits interval dominated convergence as `c -> 1+`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiArithmeticPoleRemainder

open MeasureTheory
open Set
open Filter
open Complex
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1XiVerticalFunctional
open C1XiArithmeticIntervalReadback
open C1XiArithmeticPoleBoundary
open C1XiResidue
open scoped BigOperators Interval Topology

noncomputable section

/-- The derivative of the compact-log Laplace transform. -/
noncomputable def laplaceAtDerivative
    (F : CompactLogTest) (s : Complex) : Complex :=
  ∫ x : Real, (Complex.exp (s * (x : Complex)) * (x : Complex)) * F.test x

theorem hasDerivAt_laplaceAt_with_derivative
    (F : CompactLogTest) (s : Complex) :
    HasDerivAt
      (fun z : Complex => CompactLogTest.laplaceAt F z)
      (laplaceAtDerivative F s) s := by
  simpa only [laplaceAtDerivative] using hasDerivAt_laplaceAt F s

theorem continuous_laplaceAtDerivative (F : CompactLogTest) :
    Continuous (laplaceAtDerivative F) := by
  obtain ⟨K, hK, hzero⟩ :=
    (exists_compact_iff_hasCompactSupport (f := F.test)).mpr F.compactSupport
  let integrand : Complex → Real → Complex := fun s x =>
    (Complex.exp (s * (x : Complex)) * (x : Complex)) * F.test x
  have hcont : Continuous (Function.uncurry integrand) := by
    change Continuous (fun p : Complex × Real =>
      (Complex.exp (p.1 * (p.2 : Complex)) * (p.2 : Complex)) * F.test p.2)
    exact
      ((Complex.continuous_exp.comp
        (continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd))).mul
          (Complex.continuous_ofReal.comp continuous_snd)).mul
        (F.test.continuous.comp continuous_snd)
  have hparam : Continuous (fun s : Complex => ∫ x in K, integrand s x) :=
    continuous_parametric_integral_of_continuous hcont hK
  have heq :
      (fun s : Complex => ∫ x in K, integrand s x) =
        (fun s : Complex => laplaceAtDerivative F s) := by
    funext s
    calc
      (∫ x in K, integrand s x) = ∫ x : Real, integrand s x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        simp [integrand, hzero x hx]
      _ = laplaceAtDerivative F s := by
        rfl
  change Continuous (fun s : Complex => laplaceAtDerivative F s)
  rw [← heq]
  exact hparam

/-- Derivative of the centered weight, in the same owner as the contour weight. -/
noncomputable def centeredLaplaceWeightDerivative
    (F : CompactLogTest) (s : Complex) : Complex :=
  laplaceAtDerivative F (s - (1 / 2 : Complex))

theorem hasDerivAt_centeredLaplaceWeight
    (F : CompactLogTest) (s : Complex) :
    HasDerivAt (centeredLaplaceWeight F)
      (centeredLaplaceWeightDerivative F s) s := by
  have hsub : HasDerivAt
      (fun z : Complex => z - (1 / 2 : Complex)) 1 s := by
    simpa using (hasDerivAt_id s).sub_const (1 / 2 : Complex)
  have hcomp :=
    (hasDerivAt_laplaceAt_with_derivative F (s - (1 / 2 : Complex))).comp s hsub
  simpa only [centeredLaplaceWeight, centeredLaplaceWeightDerivative, mul_one] using hcomp

theorem continuous_centeredLaplaceWeightDerivative (F : CompactLogTest) :
    Continuous (centeredLaplaceWeightDerivative F) := by
  unfold centeredLaplaceWeightDerivative
  exact (continuous_laplaceAtDerivative F).comp
    (continuous_id.sub continuous_const)

theorem continuous_symmetrizedLaplaceWeight (F : CompactLogTest) :
    Continuous (symmetrizedLaplaceWeight F) := by
  unfold symmetrizedLaplaceWeight
  apply Continuous.add
  · exact continuous_centeredLaplaceWeight F
  · exact (continuous_centeredLaplaceWeight F).comp
      (continuous_const.sub continuous_id)

/-- Derivative of the functional-equation-symmetric weight. -/
noncomputable def symmetrizedLaplaceWeightDerivative
    (F : CompactLogTest) (s : Complex) : Complex :=
  centeredLaplaceWeightDerivative F s -
    centeredLaplaceWeightDerivative F (1 - s)

theorem hasDerivAt_symmetrizedLaplaceWeight
    (F : CompactLogTest) (s : Complex) :
    HasDerivAt (symmetrizedLaplaceWeight F)
      (symmetrizedLaplaceWeightDerivative F s) s := by
  have hfirst := hasDerivAt_centeredLaplaceWeight F s
  have harg : HasDerivAt (fun z : Complex => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : Complex)
  have hsecond :=
    (hasDerivAt_centeredLaplaceWeight F (1 - s)).comp s harg
  have hsum := hfirst.add hsecond
  simpa only [symmetrizedLaplaceWeight, symmetrizedLaplaceWeightDerivative,
    Function.comp_apply, neg_mul, mul_neg, mul_one, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hsum

theorem continuous_symmetrizedLaplaceWeightDerivative (F : CompactLogTest) :
    Continuous (symmetrizedLaplaceWeightDerivative F) := by
  unfold symmetrizedLaplaceWeightDerivative
  exact (continuous_centeredLaplaceWeightDerivative F).sub
    ((continuous_centeredLaplaceWeightDerivative F).comp
      (continuous_const.sub continuous_id))

private theorem continuous_symmetrizedLaplaceWeight_vertical_remainder
    (F : CompactLogTest) :
    Continuous (fun p : Real × Real =>
      symmetrizedLaplaceWeight F (verticalPoint p.1 p.2)) := by
  exact (continuous_symmetrizedLaplaceWeight F).comp (by
    unfold verticalPoint
    fun_prop)

noncomputable def verticalSymmetrizedLaplaceWeightDerivative
    (F : CompactLogTest) (c t : Real) : Complex :=
  symmetrizedLaplaceWeightDerivative F (verticalPoint c t) * Complex.I

theorem hasDerivAt_symmetrizedLaplaceWeight_vertical
    (F : CompactLogTest) (c t : Real) :
    HasDerivAt
      (fun u : Real => symmetrizedLaplaceWeight F (verticalPoint c u))
      (verticalSymmetrizedLaplaceWeightDerivative F c t) t := by
  have hlin : HasDerivAt
      (fun u : Real => (u : Complex) * Complex.I) Complex.I t := by
    simpa using
      (hasDerivAt_mul_const Complex.I (x := (t : Complex))).comp_ofReal
  have hconst : HasDerivAt (fun _ : Real => (c : Complex)) 0 t :=
    hasDerivAt_const t (c : Complex)
  have hpoint : HasDerivAt (fun u : Real => verticalPoint c u) Complex.I t := by
    simpa only [verticalPoint, zero_add] using hconst.add hlin
  have hcomp :=
    (hasDerivAt_symmetrizedLaplaceWeight F (verticalPoint c t)).scomp t hpoint
  simpa only [Function.comp_apply, verticalSymmetrizedLaplaceWeightDerivative,
    smul_eq_mul, mul_comm] using hcomp

theorem continuous_verticalSymmetrizedLaplaceWeightDerivative
    (F : CompactLogTest) :
    Continuous (fun p : Real × Real =>
      verticalSymmetrizedLaplaceWeightDerivative F p.1 p.2) := by
  unfold verticalSymmetrizedLaplaceWeightDerivative
  have hpoint : Continuous (fun p : Real × Real => verticalPoint p.1 p.2) := by
    unfold verticalPoint
    fun_prop
  exact ((continuous_symmetrizedLaplaceWeightDerivative F).comp hpoint).mul
    continuous_const

/-- The compact-rectangle difference quotient estimate for the actual weight. -/
theorem exists_symmetrizedLaplaceWeight_vertical_difference_bound
    (F : CompactLogTest) {T : Real} (hT : 0 ≤ T) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ c ∈ Icc (1 : Real) 2, ∀ t ∈ Icc (-T) T,
        ‖symmetrizedLaplaceWeight F (verticalPoint c t) -
          symmetrizedLaplaceWeight F (verticalPoint c 0)‖ ≤ C * |t| := by
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (continuous_verticalSymmetrizedLaplaceWeightDerivative F).continuousOn
  let C : Real := max C₀ 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro c hc t ht
  let f : Real → Complex := fun u =>
    symmetrizedLaplaceWeight F (verticalPoint c u)
  let f' : Real → Complex := fun u =>
    verticalSymmetrizedLaplaceWeightDerivative F c u
  have hdiff : ∀ u ∈ Icc (-T) T, DifferentiableAt Real f u := by
    intro u hu
    simpa only [f] using
      (hasDerivAt_symmetrizedLaplaceWeight_vertical F c u).differentiableAt
  have hbound : ∀ u ∈ Icc (-T) T, ‖f' u‖ ≤ C := by
    intro u hu
    have hrect : (c, u) ∈ Icc (1 : Real) 2 ×ˢ Icc (-T) T := ⟨hc, hu⟩
    exact (hC₀ (c, u) hrect).trans (le_max_left _ _)
  have hbound' : ∀ u ∈ Icc (-T) T, ‖deriv f u‖ ≤ C := by
    intro u hu
    rw [(hasDerivAt_symmetrizedLaplaceWeight_vertical F c u).deriv]
    exact hbound u hu
  have hzero : (0 : Real) ∈ Icc (-T) T := by
    exact ⟨neg_nonpos.mpr hT, hT⟩
  have hmvt :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound'
      (convex_Icc (-T) T) hzero ht
  simpa only [f, f', sub_zero, Real.norm_eq_abs] using hmvt

private def poleBoundaryParameter (k : Nat) : Real :=
  1 + (((k + 1 : Nat) : Real)⁻¹)

private theorem poleBoundaryParameter_gt_one (k : Nat) :
    1 < poleBoundaryParameter k := by
  unfold poleBoundaryParameter
  have hpos : 0 < ((k + 1 : Nat) : Real) := by positivity
  linarith [inv_pos.mpr hpos]

private theorem poleBoundaryParameter_le_two (k : Nat) :
    poleBoundaryParameter k ≤ 2 := by
  unfold poleBoundaryParameter
  have hone : (1 : Real) ≤ ((k + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hinv : ((k + 1 : Nat) : Real)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 hone
  linarith

private theorem poleBoundaryParameter_tendsto_one :
    Tendsto poleBoundaryParameter atTop (𝓝 (1 : Real)) := by
  have hshift : Tendsto (fun k : Nat => k + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hinv : Tendsto
      (fun k : Nat => ((k + 1 : Nat) : Real)⁻¹) atTop (𝓝 (0 : Real)) := by
    simpa only [Function.comp_apply] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := Real)).comp hshift
  change Tendsto
    (fun k : Nat => (1 : Real) + ((k + 1 : Nat) : Real)⁻¹)
    atTop (𝓝 (1 : Real))
  simpa only [add_zero] using
    (tendsto_const_nhds (x := (1 : Real))).add hinv

private theorem continuous_elementaryPoleSingularRemainder_of_gt_one
    (F : CompactLogTest) {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real => elementaryPoleSingularRemainder F c t) := by
  unfold elementaryPoleSingularRemainder
  have hpoint : Continuous (fun t : Real => verticalPoint c t) := by
    unfold verticalPoint
    fun_prop
  have hzero : ∀ t : Real, verticalPoint c t - 1 ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [verticalPoint] at hre
    linarith
  have hkernel : Continuous (fun t : Real => elementaryPoleSingularKernel c t) := by
    unfold elementaryPoleSingularKernel
    exact (continuous_const.div (hpoint.sub continuous_const) hzero).neg.mul
      continuous_const
  exact hkernel.mul ((continuous_symmetrizedLaplaceWeight F).comp hpoint |>.sub
    continuous_const)

private theorem norm_elementaryPoleSingularKernel
    {c t : Real} :
    ‖elementaryPoleSingularKernel c t‖ =
      ‖verticalPoint c t - 1‖⁻¹ := by
  simp [elementaryPoleSingularKernel]

private theorem elementaryPoleSingularRemainder_norm_le_of_parameter
    (F : CompactLogTest) {T : Real}
    {C : Real} (hC : 0 ≤ C)
    (hweight : ∀ c ∈ Icc (1 : Real) 2, ∀ t ∈ Icc (-T) T,
      ‖symmetrizedLaplaceWeight F (verticalPoint c t) -
        symmetrizedLaplaceWeight F (verticalPoint c 0)‖ ≤ C * |t|)
    (k : Nat) (t : Real) (ht : t ∈ Icc (-T) T) :
    ‖elementaryPoleSingularRemainder F (poleBoundaryParameter k) t‖ ≤ C := by
  have hc : 1 < poleBoundaryParameter k := poleBoundaryParameter_gt_one k
  have hcIcc : poleBoundaryParameter k ∈ Icc (1 : Real) 2 :=
    ⟨hc.le, poleBoundaryParameter_le_two k⟩
  have hdiff := hweight (poleBoundaryParameter k) hcIcc t ht
  by_cases ht0 : t = 0
  · simp [elementaryPoleSingularRemainder, ht0]
    exact hC
  · let z : Complex := verticalPoint (poleBoundaryParameter k) t - 1
    have hz : z ≠ 0 := by
      dsimp [z]
      intro h
      have hre := congrArg Complex.re h
      simp [verticalPoint] at hre
      linarith [hc]
    have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have himag : |t| ≤ ‖z‖ := by
      dsimp [z]
      simpa [verticalPoint] using abs_im_le_norm
        (verticalPoint (poleBoundaryParameter k) t - 1)
    have hratio : ‖z‖⁻¹ * |t| ≤ 1 := by
      calc
        ‖z‖⁻¹ * |t| ≤ ‖z‖⁻¹ * ‖z‖ :=
          mul_le_mul_of_nonneg_left himag (inv_nonneg.mpr hznorm.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hznorm)
    calc
      ‖elementaryPoleSingularRemainder F (poleBoundaryParameter k) t‖ =
          ‖elementaryPoleSingularKernel (poleBoundaryParameter k) t‖ *
            ‖symmetrizedLaplaceWeight F
                (verticalPoint (poleBoundaryParameter k) t) -
              symmetrizedLaplaceWeight F
                (verticalPoint (poleBoundaryParameter k) 0)‖ := by
        rw [elementaryPoleSingularRemainder, norm_mul]
      _ = ‖z‖⁻¹ *
          ‖symmetrizedLaplaceWeight F
              (verticalPoint (poleBoundaryParameter k) t) -
            symmetrizedLaplaceWeight F
              (verticalPoint (poleBoundaryParameter k) 0)‖ := by
        rw [norm_elementaryPoleSingularKernel]
      _ ≤ ‖z‖⁻¹ * (C * |t|) := by
        exact mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hznorm.le)
      _ = C * (‖z‖⁻¹ * |t|) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hratio hC
      _ = C := by ring

theorem exists_elementaryPoleSingularRemainder_uniform_bound
    (F : CompactLogTest) {T : Real} (hT : 0 < T) :
    ∃ C : Real, 0 ≤ C ∧ ∀ k : Nat, ∀ t ∈ Icc (-T) T,
      ‖elementaryPoleSingularRemainder F (poleBoundaryParameter k) t‖ ≤ C := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_symmetrizedLaplaceWeight_vertical_difference_bound F hT.le
  refine ⟨C, hC, ?_⟩
  intro k t ht
  exact elementaryPoleSingularRemainder_norm_le_of_parameter F hC hweight k t ht

noncomputable def elementaryPoleSingularRemainderBoundaryIntegrand
    (F : CompactLogTest) (t : Real) : Complex :=
  if t = 0 then 0 else
    elementaryPoleSingularKernel 1 t *
      (symmetrizedLaplaceWeight F (verticalPoint 1 t) -
        symmetrizedLaplaceWeight F (verticalPoint 1 0))

noncomputable def elementaryPoleSingularRemainderBoundaryValue
    (F : CompactLogTest) (T : Real) : Complex :=
  ∫ t : Real in (-T)..T,
    elementaryPoleSingularRemainderBoundaryIntegrand F t

private theorem tendsto_elementaryPoleSingularRemainder_at_ne_zero
    (F : CompactLogTest) {t : Real} (ht : t ≠ 0) :
    Tendsto
      (fun k : Nat => elementaryPoleSingularRemainder F
        (poleBoundaryParameter k) t)
      atTop
      (𝓝 (elementaryPoleSingularRemainderBoundaryIntegrand F t)) := by
  have hc := poleBoundaryParameter_tendsto_one
  have hvertical : Continuous (fun c : Real => verticalPoint c t) := by
    unfold verticalPoint
    fun_prop
  have hzero : verticalPoint 1 t - 1 ≠ 0 := by
    intro h
    apply ht
    have him := congrArg Complex.im h
    simpa [verticalPoint] using him
  have hkernel : ContinuousAt
      (fun c : Real => elementaryPoleSingularKernel c t) 1 := by
    unfold elementaryPoleSingularKernel
    exact (continuousAt_const.div
      (hvertical.continuousAt.sub continuousAt_const) hzero).neg.mul
      continuousAt_const
  have hweight : ContinuousAt
      (fun c : Real =>
        symmetrizedLaplaceWeight F (verticalPoint c t) -
          symmetrizedLaplaceWeight F (verticalPoint c 0)) 1 := by
    have hzeroPoint : Continuous (fun c : Real => verticalPoint c 0) := by
      unfold verticalPoint
      fun_prop
    exact ((continuous_symmetrizedLaplaceWeight F).comp hvertical).continuousAt.sub
      ((continuous_symmetrizedLaplaceWeight F).comp hzeroPoint).continuousAt
  have hprod := hkernel.tendsto.mul hweight.tendsto
  simpa only [elementaryPoleSingularRemainder,
    elementaryPoleSingularRemainderBoundaryIntegrand, if_neg ht] using
    hprod.comp hc

theorem tendsto_elementaryPoleSingularRemainder_intervalIntegral
    (F : CompactLogTest) {T : Real} (hT : 0 < T) :
    Tendsto
      (fun k : Nat => ∫ t : Real in (-T)..T,
        elementaryPoleSingularRemainder F (poleBoundaryParameter k) t)
      atTop
      (𝓝 (elementaryPoleSingularRemainderBoundaryValue F T)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_elementaryPoleSingularRemainder_uniform_bound F hT
  have hmeas : ∀ᶠ k : Nat in atTop,
      AEStronglyMeasurable
        (fun t : Real => elementaryPoleSingularRemainder F
          (poleBoundaryParameter k) t)
        (volume.restrict (Ι (-T) T)) := by
    filter_upwards [] with k
    exact (continuous_elementaryPoleSingularRemainder_of_gt_one F
      (poleBoundaryParameter_gt_one k)).aestronglyMeasurable
  have hbound_ae : ∀ᶠ k : Nat in atTop, ∀ᵐ t : Real ∂volume,
      t ∈ Ι (-T) T →
        ‖elementaryPoleSingularRemainder F (poleBoundaryParameter k) t‖ ≤ C := by
    filter_upwards [] with k
    filter_upwards [] with t ht
    have htcc : t ∈ Icc (-T) T := by
      simpa only [uIcc_of_le (by linarith : -T ≤ T)] using
        (uIoc_subset_uIcc ht)
    exact hbound k t htcc
  have hlim : ∀ᵐ t : Real ∂volume, t ∈ Ι (-T) T →
      Tendsto
        (fun k : Nat => elementaryPoleSingularRemainder F
          (poleBoundaryParameter k) t)
        atTop
        (𝓝 (elementaryPoleSingularRemainderBoundaryIntegrand F t)) := by
    filter_upwards [volume.ae_ne (0 : Real)] with t ht0 ht
    exact tendsto_elementaryPoleSingularRemainder_at_ne_zero F ht0
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : Real => C) hmeas hbound_ae intervalIntegrable_const hlim

noncomputable def concreteElementaryPoleSingularRemainderBoundaryContract
    (F : CompactLogTest) {T : Real} (hT : 0 < T) :
    ElementaryPoleSingularRemainderBoundaryContract F T := by
  refine
    { c := poleBoundaryParameter
      c_gt_one := poleBoundaryParameter_gt_one
      c_tendsto_one := poleBoundaryParameter_tendsto_one
      remainderBoundaryValue := elementaryPoleSingularRemainderBoundaryValue F T
      remainder_integral_tendsto := ?_ }
  exact tendsto_elementaryPoleSingularRemainder_intervalIntegral F hT

end
end C1XiArithmeticPoleRemainder
end Source
end ConnesWeilRH
