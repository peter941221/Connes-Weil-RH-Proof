import ConnesWeilRH.Dev.C1XiArithmeticIntervalReadback
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# C1XiArithmeticPoleBoundary - the elementary pole boundary brick

The factor `1 / (c - 1 + t * I)` is singular at the boundary point
`(c, t) = (1, 0)`.  This module isolates its finite-height contribution
before any weighted boundary claim.  The singular kernel has an exact
arctangent integral for `c > 1`, and its right-hand limit is the principal
value `-pi * I`.  The weighted remainder is kept as an explicit contract:
pointwise convergence away from `t = 0` is not an integral boundary theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiArithmeticPoleBoundary

open MeasureTheory
open Set
open Filter
open Complex
open CCM25Concrete.CompactLogConvolution
open C1XiVerticalFunctional
open C1XiArithmeticIntervalReadback
open C1XiResidue
open scoped BigOperators Interval Topology

noncomputable section

/-- The singular elementary-pole factor with the vertical orientation included. -/
noncomputable def elementaryPoleSingularKernel (c t : Real) : Complex :=
  -(1 / (verticalPoint c t - 1)) * Complex.I

/-- The regular elementary-pole factor, separated from the boundary singularity. -/
noncomputable def elementaryPoleRegularKernel (c t : Real) : Complex :=
  -(1 / verticalPoint c t) * Complex.I

/-- The singular factor multiplied by the centered symmetric test weight. -/
noncomputable def elementaryPoleSingularIntegrand
    (F : CompactLogTest) (c t : Real) : Complex :=
  elementaryPoleSingularKernel c t *
    symmetrizedLaplaceWeight F (verticalPoint c t)

/-- The regular factor multiplied by the centered symmetric test weight. -/
noncomputable def elementaryPoleRegularIntegrand
    (F : CompactLogTest) (c t : Real) : Complex :=
  elementaryPoleRegularKernel c t *
    symmetrizedLaplaceWeight F (verticalPoint c t)

/-- The weighted singular remainder after subtracting the value at `t = 0`. -/
noncomputable def elementaryPoleSingularRemainder
    (F : CompactLogTest) (c t : Real) : Complex :=
  elementaryPoleSingularKernel c t *
    (symmetrizedLaplaceWeight F (verticalPoint c t) -
      symmetrizedLaplaceWeight F (verticalPoint c 0))

private theorem continuous_positive_verticalPoint_pole :
    Continuous (fun p : {c : Real // 0 < c} × Real =>
      verticalPoint p.1.1 p.2) := by
  unfold verticalPoint
  fun_prop

private theorem continuous_symmetrizedWeight_positive_vertical_pole
    (F : CompactLogTest) :
    Continuous (fun p : {c : Real // 0 < c} × Real =>
      symmetrizedLaplaceWeight F (verticalPoint p.1.1 p.2)) := by
  unfold symmetrizedLaplaceWeight
  apply Continuous.add
  · exact (continuous_centeredLaplaceWeight F).comp
      continuous_positive_verticalPoint_pole
  · exact (continuous_centeredLaplaceWeight F).comp
      (continuous_const.sub continuous_positive_verticalPoint_pole)

private theorem continuous_elementaryPoleRegularIntegrand_positive_vertical
    (F : CompactLogTest) :
    Continuous (fun p : {c : Real // 0 < c} × Real =>
      elementaryPoleRegularIntegrand F p.1.1 p.2) := by
  unfold elementaryPoleRegularIntegrand elementaryPoleRegularKernel
  have hzero : ∀ p : {c : Real // 0 < c} × Real,
      verticalPoint p.1.1 p.2 ≠ 0 := by
    intro p h
    have hre := congrArg Complex.re h
    simp [verticalPoint] at hre
    linarith [p.1.2]
  have hkernel : Continuous (fun p : {c : Real // 0 < c} × Real =>
      -(1 / verticalPoint p.1.1 p.2) * Complex.I) := by
    exact (continuous_const.div continuous_positive_verticalPoint_pole hzero).neg.mul
      continuous_const
  exact hkernel.mul (continuous_symmetrizedWeight_positive_vertical_pole F)

/-- Continuity of the regular elementary-pole interval integral on `0 < c`. -/
theorem continuous_elementaryPoleRegularIntegrand_intervalIntegral
    (F : CompactLogTest) (T : Real) :
    Continuous (fun c : {c : Real // 0 < c} =>
      ∫ t : Real in (-T)..T, elementaryPoleRegularIntegrand F c t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · simpa only [Function.uncurry] using
      (continuous_elementaryPoleRegularIntegrand_positive_vertical F)
  · exact continuous_const

/-- The regular pole contribution has an ordinary right-hand `c -> 1` limit. -/
theorem tendsto_elementaryPoleRegularIntegrand_intervalIntegral_c_to_one
    (F : CompactLogTest) (T : Real) :
    Tendsto
      (fun c : Real =>
        ∫ t : Real in (-T)..T, elementaryPoleRegularIntegrand F c t)
      (𝓝[>] (1 : Real))
      (𝓝 (∫ t : Real in (-T)..T, elementaryPoleRegularIntegrand F 1 t)) := by
  let liftC : Real → {c : Real // 0 < c} := fun c =>
    ⟨max c (1 / 2 : Real), by positivity⟩
  have hmax : Tendsto (fun c : Real => max c (1 / 2 : Real))
      (𝓝[>] (1 : Real)) (𝓝 (1 : Real)) := by
    have hid : Tendsto (fun c : Real => c)
        (𝓝[>] (1 : Real)) (𝓝 (1 : Real)) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : Real => (1 / 2 : Real))
        (𝓝[>] (1 : Real)) (𝓝 (1 / 2 : Real)) :=
      tendsto_const_nhds
    simpa only [max_eq_left (by norm_num : (1 / 2 : Real) ≤ 1)] using hid.max hconst
  have hlift : Tendsto liftC (𝓝[>] (1 : Real))
      (𝓝 (⟨1, by norm_num⟩ : {c : Real // 0 < c})) := by
    exact tendsto_subtype_rng.mpr hmax
  have hcont : Tendsto
      (fun c : Real =>
        ∫ t : Real in (-T)..T, elementaryPoleRegularIntegrand F (liftC c) t)
      (𝓝[>] (1 : Real))
      (𝓝 (∫ t : Real in (-T)..T,
        elementaryPoleRegularIntegrand F (⟨1, by norm_num⟩ : {c : Real // 0 < c}) t)) := by
    simpa only [Function.comp_apply] using
      ((continuous_elementaryPoleRegularIntegrand_intervalIntegral F T).continuousAt.tendsto.comp
        hlift)
  have heq :
      (fun c : Real =>
        ∫ t : Real in (-T)..T, elementaryPoleRegularIntegrand F (liftC c) t) =ᶠ[𝓝[>] (1 : Real)]
      (fun c : Real =>
        ∫ t : Real in (-T)..T, elementaryPoleRegularIntegrand F c t) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc' : 1 < c := hc
    have hcmax : max c (1 / 2 : Real) = c := by
      exact max_eq_left (by linarith [hc'])
    simp only [liftC]
    rw [hcmax]
  simpa using hcont.congr' heq

private theorem verticalPoint_sub_one_eq (c t : Real) :
    verticalPoint c t - 1 = ((c - 1 : Real) : Complex) + (t : Complex) * Complex.I := by
  apply Complex.ext <;> simp [verticalPoint]

private theorem continuous_symmetrizedLaplaceWeight_vertical_fixed
    (F : CompactLogTest) (c : Real) :
    Continuous (fun t : Real =>
      symmetrizedLaplaceWeight F (verticalPoint c t)) := by
  have hpoint : Continuous (fun t : Real => verticalPoint c t) := by
    unfold verticalPoint
    fun_prop
  unfold symmetrizedLaplaceWeight
  apply Continuous.add
  · exact (continuous_centeredLaplaceWeight F).comp hpoint
  · exact (continuous_centeredLaplaceWeight F).comp
      (continuous_const.sub hpoint)

private theorem continuous_elementaryPoleSingularKernel_of_gt_one
    {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real => elementaryPoleSingularKernel c t) := by
  unfold elementaryPoleSingularKernel
  have hpoint : Continuous (fun t : Real => verticalPoint c t) := by
    unfold verticalPoint
    fun_prop
  have hzero : ∀ t : Real, verticalPoint c t - 1 ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [verticalPoint] at hre
    linarith [hc]
  exact (continuous_const.div (hpoint.sub continuous_const) hzero).neg.mul
    continuous_const

private theorem continuous_elementaryPoleRegularIntegrand_of_gt_one
    (F : CompactLogTest) {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real => elementaryPoleRegularIntegrand F c t) := by
  unfold elementaryPoleRegularIntegrand elementaryPoleRegularKernel
  have hpoint : Continuous (fun t : Real => verticalPoint c t) := by
    unfold verticalPoint
    fun_prop
  have hzero : ∀ t : Real, verticalPoint c t ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [verticalPoint] at hre
    linarith [hc]
  have hkernel : Continuous (fun t : Real =>
      -(1 / verticalPoint c t) * Complex.I) := by
    exact (continuous_const.div hpoint hzero).neg.mul continuous_const
  exact hkernel.mul (continuous_symmetrizedLaplaceWeight_vertical_fixed F c)

private theorem continuous_elementaryPoleSingularIntegrand_of_gt_one
    (F : CompactLogTest) {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real => elementaryPoleSingularIntegrand F c t) := by
  unfold elementaryPoleSingularIntegrand
  exact (continuous_elementaryPoleSingularKernel_of_gt_one hc).mul
    (continuous_symmetrizedLaplaceWeight_vertical_fixed F c)

private theorem continuous_elementaryPoleSingularRemainder_of_gt_one
    (F : CompactLogTest) {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real => elementaryPoleSingularRemainder F c t) := by
  unfold elementaryPoleSingularRemainder
  exact (continuous_elementaryPoleSingularKernel_of_gt_one hc).mul
    ((continuous_symmetrizedLaplaceWeight_vertical_fixed F c).sub continuous_const)

private theorem intervalIntegrable_elementaryPoleRegularIntegrand_of_gt_one
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    IntervalIntegrable
      (fun t : Real => elementaryPoleRegularIntegrand F c t) volume (-T) T :=
  (continuous_elementaryPoleRegularIntegrand_of_gt_one F hc).intervalIntegrable _ _

private theorem intervalIntegrable_elementaryPoleSingularKernel_of_gt_one
    {c T : Real} (hc : 1 < c) :
    IntervalIntegrable
      (fun t : Real => elementaryPoleSingularKernel c t) volume (-T) T :=
  (continuous_elementaryPoleSingularKernel_of_gt_one hc).intervalIntegrable _ _

private theorem intervalIntegrable_elementaryPoleSingularIntegrand_of_gt_one
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    IntervalIntegrable
      (fun t : Real => elementaryPoleSingularIntegrand F c t) volume (-T) T :=
  (continuous_elementaryPoleSingularIntegrand_of_gt_one F hc).intervalIntegrable _ _

private theorem intervalIntegrable_elementaryPoleSingularRemainder_of_gt_one
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    IntervalIntegrable
      (fun t : Real => elementaryPoleSingularRemainder F c t) volume (-T) T :=
  (continuous_elementaryPoleSingularRemainder_of_gt_one F hc).intervalIntegrable _ _

private theorem elementaryPoleSingularKernel_eq_real_parts
    {c t : Real} (hc : 1 < c) :
    elementaryPoleSingularKernel c t =
      ((-t / ((c - 1) ^ 2 + t ^ 2) : Real) : Complex) +
        ((-(c - 1) / ((c - 1) ^ 2 + t ^ 2) : Real) : Complex) * Complex.I := by
  have hδ : 0 < c - 1 := by linarith
  have hden : 0 < (c - 1) ^ 2 + t ^ 2 := by positivity
  have hden' : 0 < 1 - c * 2 + c ^ 2 + t ^ 2 := by
    nlinarith
  have hdenC : (((c - 1) ^ 2 + t ^ 2 : Real) : Complex) ≠ 0 := by
    exact_mod_cast (ne_of_gt hden)
  have hden'C : ((1 - c * 2 + c ^ 2 + t ^ 2 : Real) : Complex) ≠ 0 := by
    exact_mod_cast (ne_of_gt hden')
  have hden''C :
      (1 - (c : Complex) * 2 + (c : Complex) ^ 2 + (t : Complex) ^ 2) ≠ 0 := by
    convert hden'C using 1 <;> push_cast <;> ring
  have hpoint : verticalPoint c t - 1 =
      ((c - 1 : Real) : Complex) + (t : Complex) * Complex.I :=
    verticalPoint_sub_one_eq c t
  have hz : ((c - 1 : Real) : Complex) + (t : Complex) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hmul :
      (((c - 1 : Real) : Complex) + (t : Complex) * Complex.I) *
          (((c - 1 : Real) : Complex) - (t : Complex) * Complex.I) =
        (((c - 1) ^ 2 + t ^ 2 : Real) : Complex) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [elementaryPoleSingularKernel, hpoint]
  field_simp [hz, hdenC, ne_of_gt hden]
  push_cast
  ring_nf
  field_simp [hden'C, hden''C]
  ring_nf
  try simp only [Complex.I_mul_I, Complex.I_sq]
  ring

private theorem intervalIntegrable_singular_real_parts
    {c T : Real} (hc : 1 < c) :
    IntervalIntegrable
        (fun t : Real => -t / ((c - 1) ^ 2 + t ^ 2)) volume (-T) T := by
  have hδ : 0 < c - 1 := by linarith
  have hden : ∀ t : Real, (c - 1) ^ 2 + t ^ 2 ≠ 0 := by
    intro t
    positivity
  have hdenCont : Continuous (fun t : Real => (c - 1) ^ 2 + t ^ 2) := by
    fun_prop
  exact ((continuous_id.neg.div hdenCont hden).intervalIntegrable _ _)

private theorem intervalIntegrable_singular_imaginary_parts
    {c T : Real} (hc : 1 < c) :
    IntervalIntegrable
        (fun t : Real => -(c - 1) / ((c - 1) ^ 2 + t ^ 2)) volume (-T) T := by
  have hδ : 0 < c - 1 := by linarith
  have hden : ∀ t : Real, (c - 1) ^ 2 + t ^ 2 ≠ 0 := by
    intro t
    positivity
  have hdenCont : Continuous (fun t : Real => (c - 1) ^ 2 + t ^ 2) := by
    fun_prop
  exact ((continuous_const.neg.div hdenCont hden).intervalIntegrable _ _)

private theorem continuous_singular_real_part
    {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real => -t / ((c - 1) ^ 2 + t ^ 2)) := by
  have hden : ∀ t : Real, (c - 1) ^ 2 + t ^ 2 ≠ 0 := by
    intro t
    positivity
  have hdenCont : Continuous (fun t : Real => (c - 1) ^ 2 + t ^ 2) := by
    fun_prop
  exact continuous_id.neg.div hdenCont hden

private theorem continuous_singular_imaginary_part
    {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real => -(c - 1) / ((c - 1) ^ 2 + t ^ 2)) := by
  have hden : ∀ t : Real, (c - 1) ^ 2 + t ^ 2 ≠ 0 := by
    intro t
    positivity
  have hdenCont : Continuous (fun t : Real => (c - 1) ^ 2 + t ^ 2) := by
    fun_prop
  exact continuous_const.neg.div hdenCont hden

private theorem singular_real_part_integral_eq_zero
    {c T : Real} (hc : 1 < c) :
    (∫ t : Real in (-T)..T, -t / ((c - 1) ^ 2 + t ^ 2)) = 0 := by
  let f : Real → Real := fun t => -t / ((c - 1) ^ 2 + t ^ 2)
  have hf : IntervalIntegrable f volume (-T) T := by
    simpa [f] using intervalIntegrable_singular_real_parts hc
  have hodd : ∀ t : Real, f (-t) = -f t := by
    intro t
    dsimp [f]
    ring_nf
  have hcomp := intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
  have hcomp' : (∫ t : Real in (-T)..T, -f t) = ∫ t : Real in (-T)..T, f t := by
    simpa only [hodd, neg_neg] using hcomp
  rw [intervalIntegral.integral_neg] at hcomp'
  linarith

/-- Exact finite-height integral of the unweighted singular elementary-pole kernel. -/
theorem integral_elementaryPoleSingularKernel
    {c T : Real} (hc : 1 < c) :
    (∫ t : Real in (-T)..T, elementaryPoleSingularKernel c t) =
      ((-(2 * Real.arctan (T / (c - 1))) : Real) : Complex) * Complex.I := by
  have hδ : 0 < c - 1 := by linarith
  have hreal : IntervalIntegrable
      (fun t : Real => -t / ((c - 1) ^ 2 + t ^ 2)) volume (-T) T :=
    intervalIntegrable_singular_real_parts hc
  have himag : IntervalIntegrable
      (fun t : Real => -(c - 1) / ((c - 1) ^ 2 + t ^ 2)) volume (-T) T :=
    intervalIntegrable_singular_imaginary_parts hc
  have hrealC : IntervalIntegrable
      (fun t : Real => ((-t / ((c - 1) ^ 2 + t ^ 2) : Real) : Complex))
      volume (-T) T :=
    (Complex.continuous_ofReal.comp (continuous_singular_real_part hc)).intervalIntegrable _ _
  have himagC : IntervalIntegrable
      (fun t : Real => ((-(c - 1) / ((c - 1) ^ 2 + t ^ 2) : Real) : Complex) * Complex.I)
      volume (-T) T :=
    ((Complex.continuous_ofReal.comp (continuous_singular_imaginary_part hc)).mul
      continuous_const).intervalIntegrable _ _
  have hkernel : (fun t : Real => elementaryPoleSingularKernel c t) =
      (fun t : Real =>
        ((-t / ((c - 1) ^ 2 + t ^ 2) : Real) : Complex) +
          ((-(c - 1) / ((c - 1) ^ 2 + t ^ 2) : Real) : Complex) * Complex.I) := by
    funext t
    exact elementaryPoleSingularKernel_eq_real_parts hc
  rw [hkernel, intervalIntegral.integral_add hrealC himagC,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
    singular_real_part_integral_eq_zero hc]
  rw [intervalIntegral.integral_ofReal]
  rw [show (fun x : Real => -(c - 1) / ((c - 1) ^ 2 + x ^ 2)) =
      (fun x : Real => -((c - 1) / ((c - 1) ^ 2 + x ^ 2))) by
        funext x
        ring]
  rw [intervalIntegral.integral_neg, integral_div_sq_add_sq]
  have hnegfrac : -T / (c - 1) = -(T / (c - 1)) := by ring
  rw [hnegfrac, Real.arctan_neg]
  push_cast
  ring

/-- The singular kernel tends to the Cauchy principal-value constant at `c = 1`. -/
theorem tendsto_integral_elementaryPoleSingularKernel_c_to_one
    {T : Real} (hT : 0 < T) :
    Tendsto
      (fun c : Real => ∫ t : Real in (-T)..T,
        elementaryPoleSingularKernel c t)
      (𝓝[>] (1 : Real)) (𝓝 (-(Real.pi : Complex) * Complex.I)) := by
  have hdelta : Tendsto (fun c : Real => c - 1)
      (𝓝[>] (1 : Real)) (𝓝[>] (0 : Real)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    · simpa using
        ((continuousAt_id.sub continuousAt_const).tendsto.mono_left
          nhdsWithin_le_nhds :
          Tendsto (fun c : Real => c - 1) (𝓝[>] (1 : Real)) (𝓝 (1 - 1)))
    · filter_upwards [self_mem_nhdsWithin] with c hc
      have hc' : 1 < c := hc
      exact sub_pos.mpr hc'
  have hdeltaInv : Tendsto (fun c : Real => (c - 1)⁻¹)
      (𝓝[>] (1 : Real)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hdelta
  have hquot : Tendsto (fun c : Real => T / (c - 1))
      (𝓝[>] (1 : Real)) atTop := by
    have h := hdeltaInv.atTop_mul_pos hT tendsto_const_nhds
    simpa [div_eq_mul_inv, mul_comm] using h
  have hatan : Tendsto (fun c : Real => Real.arctan (T / (c - 1)))
      (𝓝[>] (1 : Real)) (𝓝 (Real.pi / 2)) := by
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hquot
  have hdouble : Tendsto (fun c : Real => 2 * Real.arctan (T / (c - 1)))
      (𝓝[>] (1 : Real)) (𝓝 (Real.pi)) := by
    convert tendsto_const_nhds.mul hatan using 1 <;> ring
  have hformula :
      (fun c : Real => ∫ t : Real in (-T)..T,
        elementaryPoleSingularKernel c t) =ᶠ[𝓝[>] (1 : Real)]
      (fun c : Real =>
        ((-(2 * Real.arctan (T / (c - 1))) : Real) : Complex) * Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact integral_elementaryPoleSingularKernel (by exact hc)
  have hlimit : Tendsto
      (fun c : Real => ((-(2 * Real.arctan (T / (c - 1))) : Real) : Complex) * Complex.I)
      (𝓝[>] (1 : Real)) (𝓝 (-(Real.pi : Complex) * Complex.I)) := by
    have hneg : Tendsto (fun c : Real => -(2 * Real.arctan (T / (c - 1))))
        (𝓝[>] (1 : Real)) (𝓝 (-Real.pi)) := by
      simpa using hdouble.neg
    have hcomplex : Tendsto (fun c : Real =>
        ((-(2 * Real.arctan (T / (c - 1))) : Real) : Complex))
        (𝓝[>] (1 : Real)) (𝓝 ((-Real.pi : Real) : Complex)) := by
      exact (Complex.continuous_ofReal.tendsto _).comp hneg
    simpa using hcomplex.mul tendsto_const_nhds
  exact hlimit.congr' hformula.symm

/-- Pointwise decomposition of the original elementary pole into regular and singular parts. -/
theorem elementaryPoleIntegrand_eq_regular_add_singular
    (F : CompactLogTest) (c t : Real) :
    elementaryPoleIntegrand F c t =
      elementaryPoleRegularIntegrand F c t +
        elementaryPoleSingularIntegrand F c t := by
  simp only [elementaryPoleIntegrand, elementaryPoleRegularIntegrand,
    elementaryPoleSingularIntegrand, elementaryPoleRegularKernel,
    elementaryPoleSingularKernel]
  ring

/-- Pointwise extraction of the singular constant from the weighted factor. -/
theorem elementaryPoleSingularIntegrand_eq_constant_add_remainder
    (F : CompactLogTest) (c t : Real) :
    elementaryPoleSingularIntegrand F c t =
      elementaryPoleSingularKernel c t *
          symmetrizedLaplaceWeight F (verticalPoint c 0) +
        elementaryPoleSingularRemainder F c t := by
  simp only [elementaryPoleSingularIntegrand, elementaryPoleSingularRemainder]
  ring

/-- A data-bearing boundary input for the weighted singular remainder. -/
structure ElementaryPoleSingularRemainderBoundaryContract
    (F : CompactLogTest) (T : Real) where
  c : Nat → Real
  c_gt_one : ∀ k, 1 < c k
  c_tendsto_one : Tendsto c atTop (𝓝 1)
  remainderBoundaryValue : Complex
  remainder_integral_tendsto : Tendsto
    (fun k => ∫ t : Real in (-T)..T, elementaryPoleSingularRemainder F (c k) t)
    atTop (𝓝 remainderBoundaryValue)

private theorem tendsto_contract_c_to_one_within
    (F : CompactLogTest) (T : Real)
    (hcontract : ElementaryPoleSingularRemainderBoundaryContract F T) :
    Tendsto hcontract.c atTop (𝓝[>] (1 : Real)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨hcontract.c_tendsto_one,
    Filter.Eventually.of_forall (fun k => hcontract.c_gt_one k)⟩

/-- Assemble the regular pole limit, the singular principal-value constant, and
the separately owned weighted remainder boundary value. -/
theorem tendsto_elementaryPoleIntegrand_intervalIntegral_of_remainderBoundaryContract
    (F : CompactLogTest) (T : Real) (hT : 0 < T)
    (hcontract : ElementaryPoleSingularRemainderBoundaryContract F T) :
    Tendsto
      (fun k : Nat =>
        ∫ t : Real in (-T)..T, elementaryPoleIntegrand F (hcontract.c k) t)
      atTop
      (𝓝 (
        (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F 1 t) +
          (-(Real.pi : Complex) * Complex.I) *
            symmetrizedLaplaceWeight F (verticalPoint 1 0) +
          hcontract.remainderBoundaryValue)) := by
  have hc_within : Tendsto hcontract.c atTop (𝓝[>] (1 : Real)) :=
    tendsto_contract_c_to_one_within F T hcontract
  have hregular : Tendsto
      (fun k : Nat =>
        ∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F (hcontract.c k) t)
      atTop
      (𝓝 (∫ t : Real in (-T)..T,
        elementaryPoleRegularIntegrand F 1 t)) := by
    simpa only [Function.comp_apply] using
      (tendsto_elementaryPoleRegularIntegrand_intervalIntegral_c_to_one F T).comp hc_within
  have hkernel : Tendsto
      (fun k : Nat =>
        ∫ t : Real in (-T)..T,
          elementaryPoleSingularKernel (hcontract.c k) t)
      atTop (𝓝 (-(Real.pi : Complex) * Complex.I)) := by
    simpa only [Function.comp_apply] using
      (tendsto_integral_elementaryPoleSingularKernel_c_to_one hT).comp hc_within
  have hweight_cont : Continuous (fun c : Real =>
      symmetrizedLaplaceWeight F (verticalPoint c 0)) := by
    have hpoint : Continuous (fun c : Real => verticalPoint c 0) := by
      unfold verticalPoint
      fun_prop
    unfold symmetrizedLaplaceWeight
    apply Continuous.add
    · exact (continuous_centeredLaplaceWeight F).comp hpoint
    · exact (continuous_centeredLaplaceWeight F).comp
        (continuous_const.sub hpoint)
  have hweight : Tendsto
      (fun k : Nat =>
        symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0))
      atTop
      (𝓝 (symmetrizedLaplaceWeight F (verticalPoint 1 0))) := by
    simpa only [Function.comp_apply] using
      hweight_cont.continuousAt.tendsto.comp hcontract.c_tendsto_one
  have hkernel_weighted : Tendsto
      (fun k : Nat =>
        (∫ t : Real in (-T)..T,
          elementaryPoleSingularKernel (hcontract.c k) t) *
          symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0))
      atTop
      (𝓝 ((-(Real.pi : Complex) * Complex.I) *
        symmetrizedLaplaceWeight F (verticalPoint 1 0))) := by
    simpa only [Function.comp_apply] using
      hkernel.mul hweight
  have hsum : Tendsto
      (fun k : Nat =>
        (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F (hcontract.c k) t) +
          (∫ t : Real in (-T)..T,
            elementaryPoleSingularKernel (hcontract.c k) t) *
            symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0) +
          ∫ t : Real in (-T)..T,
            elementaryPoleSingularRemainder F (hcontract.c k) t)
      atTop
      (𝓝 (
        (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F 1 t) +
          (-(Real.pi : Complex) * Complex.I) *
            symmetrizedLaplaceWeight F (verticalPoint 1 0) +
          hcontract.remainderBoundaryValue)) := by
    exact (hregular.add hkernel_weighted).add hcontract.remainder_integral_tendsto
  have hdecomp : ∀ k : Nat,
      (∫ t : Real in (-T)..T,
        elementaryPoleIntegrand F (hcontract.c k) t) =
        (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F (hcontract.c k) t) +
          (∫ t : Real in (-T)..T,
            elementaryPoleSingularKernel (hcontract.c k) t) *
            symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0) +
          ∫ t : Real in (-T)..T,
            elementaryPoleSingularRemainder F (hcontract.c k) t := by
    intro k
    have hc := hcontract.c_gt_one k
    have hregular_int :=
      intervalIntegrable_elementaryPoleRegularIntegrand_of_gt_one F
        (c := hcontract.c k) (T := T) hc
    have hkernel_int :=
      intervalIntegrable_elementaryPoleSingularKernel_of_gt_one
        (c := hcontract.c k) (T := T) hc
    have hsingular_int :=
      intervalIntegrable_elementaryPoleSingularIntegrand_of_gt_one F
        (c := hcontract.c k) (T := T) hc
    have hremainder_int :=
      intervalIntegrable_elementaryPoleSingularRemainder_of_gt_one F
        (c := hcontract.c k) (T := T) hc
    have hkernel_weighted_int : IntervalIntegrable
        (fun t : Real => elementaryPoleSingularKernel (hcontract.c k) t *
          symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0)) volume (-T) T :=
      ((continuous_elementaryPoleSingularKernel_of_gt_one hc).mul
        continuous_const).intervalIntegrable _ _
    have horiginal_eq :
        (fun t : Real => elementaryPoleIntegrand F (hcontract.c k) t) =
          (fun t : Real =>
            elementaryPoleRegularIntegrand F (hcontract.c k) t +
              elementaryPoleSingularIntegrand F (hcontract.c k) t) := by
      funext t
      exact elementaryPoleIntegrand_eq_regular_add_singular F _ _
    have hsingular_eq :
        (fun t : Real => elementaryPoleSingularIntegrand F (hcontract.c k) t) =
          (fun t : Real =>
            elementaryPoleSingularKernel (hcontract.c k) t *
                symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0) +
              elementaryPoleSingularRemainder F (hcontract.c k) t) := by
      funext t
      exact elementaryPoleSingularIntegrand_eq_constant_add_remainder F _ _
    calc
      (∫ t : Real in (-T)..T,
          elementaryPoleIntegrand F (hcontract.c k) t) =
          ∫ t : Real in (-T)..T,
            (elementaryPoleRegularIntegrand F (hcontract.c k) t +
              elementaryPoleSingularIntegrand F (hcontract.c k) t) := by
        rw [horiginal_eq]
      _ = (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F (hcontract.c k) t) +
          ∫ t : Real in (-T)..T,
            elementaryPoleSingularIntegrand F (hcontract.c k) t :=
        intervalIntegral.integral_add hregular_int hsingular_int
      _ = (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F (hcontract.c k) t) +
          ∫ t : Real in (-T)..T,
            (elementaryPoleSingularKernel (hcontract.c k) t *
                symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0) +
              elementaryPoleSingularRemainder F (hcontract.c k) t) := by
        rw [hsingular_eq]
      _ = (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F (hcontract.c k) t) +
          ((∫ t : Real in (-T)..T,
            elementaryPoleSingularKernel (hcontract.c k) t *
              symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0)) +
            ∫ t : Real in (-T)..T,
              elementaryPoleSingularRemainder F (hcontract.c k) t) := by
        rw [intervalIntegral.integral_add hkernel_weighted_int hremainder_int]
      _ = (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F (hcontract.c k) t) +
          (∫ t : Real in (-T)..T,
            elementaryPoleSingularKernel (hcontract.c k) t) *
              symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0) +
          ∫ t : Real in (-T)..T,
            elementaryPoleSingularRemainder F (hcontract.c k) t := by
        rw [intervalIntegral.integral_mul_const]
        ring
  have hevent :
      (fun k : Nat =>
        ∫ t : Real in (-T)..T,
          elementaryPoleIntegrand F (hcontract.c k) t) =ᶠ[atTop]
      (fun k : Nat =>
        (∫ t : Real in (-T)..T,
          elementaryPoleRegularIntegrand F (hcontract.c k) t) +
          (∫ t : Real in (-T)..T,
            elementaryPoleSingularKernel (hcontract.c k) t) *
            symmetrizedLaplaceWeight F (verticalPoint (hcontract.c k) 0) +
          ∫ t : Real in (-T)..T,
            elementaryPoleSingularRemainder F (hcontract.c k) t) :=
    Filter.Eventually.of_forall hdecomp
  exact hsum.congr' hevent.symm

end
end C1XiArithmeticPoleBoundary
end Source
end ConnesWeilRH
