/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20WindowedPairingReadback
import ConnesWeilRH.Dev.C1CC20RootWindowOperator
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The CC20 finite-rank endpoint approximant

This leaf constructs the Fourier rank-one projections used in equations
(118)--(120) of Connes--Consani, on the same ambient `L2(R)` owner as the
square-window endpoint kernel.  Every Fourier vector is zero-extended from

    I = [-log 2 / 2, log 2 / 2].

The displacement profile is cut off to `[-log 2, log 2]`; this does not change
the square-window kernel and makes its `L1` ownership explicit.  The later
finite sum is therefore finite rank by construction, rather than by a stored
rank assertion.

Reference: <https://arxiv.org/html/2006.13771#S6.SS4>.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20FiniteRankApproximation

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
open C1CC20CorrBridge C1CC20DisplacementKernel C1CC20DisplacementReadback
  C1CC20KernelLpLift C1CC20LpOperator
  C1CC20ProductIntegrability C1CC20RawKernelMass C1CC20RootWindowOperator
  C1CC20WindowedDisplacementReadback C1CC20WindowedPairingReadback

/-- The length `log 2` of the CC20 root interval. -/
noncomputable def cc20RootLength : Real := Real.log 2

theorem cc20RootLength_pos : 0 < cc20RootLength := by
  exact Real.log_pos (by norm_num)

theorem cc20RootHalfWidth_eq_half_length :
    cc20RootHalfWidth = cc20RootLength / 2 := by
  unfold cc20RootHalfWidth cc20RootLength
  rfl

/-- The only displacement values visible from the square root window. -/
def cc20RootDisplacementWindow : Set Real :=
  Set.Icc (-cc20RootLength) cc20RootLength

theorem measurableSet_cc20RootDisplacementWindow :
    MeasurableSet cc20RootDisplacementWindow := measurableSet_Icc

/-- The unnormalized Fourier mode `exp(2 pi i alpha x / log 2)`. -/
noncomputable def cc20FourierPhase (alpha x : Real) : Complex :=
  Complex.exp
    (((2 * Real.pi * alpha * x / cc20RootLength : Real) : Complex) * Complex.I)

theorem continuous_cc20FourierPhase (alpha : Real) :
    Continuous (cc20FourierPhase alpha) := by
  unfold cc20FourierPhase cc20RootLength
  fun_prop

theorem norm_cc20FourierPhase (alpha x : Real) :
    ‖cc20FourierPhase alpha x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem star_cc20FourierPhase (alpha x : Real) :
    star (cc20FourierPhase alpha x) = cc20FourierPhase (-alpha) x := by
  unfold cc20FourierPhase
  change conj (Complex.exp
      (((2 * Real.pi * alpha * x / cc20RootLength : Real) : Complex) * Complex.I)) = _
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext
  · push_cast
    simp
  · push_cast
    simp
    ring

theorem cc20FourierPhase_mul_star (alpha x y : Real) :
    cc20FourierPhase alpha x * star (cc20FourierPhase alpha y) =
      cc20FourierPhase (-alpha) (y - x) := by
  rw [star_cc20FourierPhase]
  unfold cc20FourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Fourier mode on `I`, extended by zero to the ambient real line. -/
noncomputable def cc20WindowFourierModeRaw (alpha : Real) : Real -> Complex :=
  (cc20Window cc20RootHalfWidth).indicator (cc20FourierPhase alpha)

theorem memLp_cc20WindowFourierModeRaw (alpha : Real) :
    MemLp (cc20WindowFourierModeRaw alpha) 2 volume := by
  letI : IsFiniteMeasure
      (volume.restrict (cc20Window cc20RootHalfWidth)) := by
    unfold cc20Window
    infer_instance
  rw [cc20WindowFourierModeRaw,
    memLp_indicator_iff_restrict (measurableSet_cc20Window _)]
  apply MemLp.of_bound
    ((continuous_cc20FourierPhase alpha).aestronglyMeasurable) 1
  filter_upwards with x
  rw [norm_cc20FourierPhase]

/-- The ambient `L2(R)` vector underlying the paper's projection `e_alpha`. -/
noncomputable def cc20WindowFourierVector (alpha : Real) :
    Lp Complex 2 (volume : Measure Real) :=
  (memLp_cc20WindowFourierModeRaw alpha).toLp
    (cc20WindowFourierModeRaw alpha)

theorem coeFn_cc20WindowFourierVector (alpha : Real) :
    ((cc20WindowFourierVector alpha : Lp Complex 2
        (volume : Measure Real)) : Real -> Complex) =ᵐ[volume]
      cc20WindowFourierModeRaw alpha := by
  exact (memLp_cc20WindowFourierModeRaw alpha).coeFn_toLp

/-- The normalized rank-one projection `e_alpha`.  The raw Fourier mode has
squared norm `log 2`, so the projection carries the factor `(log 2)^-1`. -/
noncomputable def cc20FourierProjection (alpha : Real) :
    Lp Complex 2 (volume : Measure Real) →L[Complex]
      Lp Complex 2 (volume : Measure Real) :=
  ((cc20RootLength⁻¹ : Real) : Complex) •
    InnerProductSpace.rankOne Complex
      (cc20WindowFourierVector alpha) (cc20WindowFourierVector alpha)

/-- The equation-(118) displacement profile of one Fourier projection,
explicitly restricted to the displacement interval seen by the square window. -/
noncomputable def cc20FourierProjectionProfile (alpha : Real) : Real -> Complex :=
  cc20RootDisplacementWindow.indicator fun v =>
    ((cc20RootLength⁻¹ : Real) : Complex) * cc20FourierPhase (-alpha) v

theorem memLp_one_cc20FourierProjectionProfile (alpha : Real) :
    MemLp (cc20FourierProjectionProfile alpha) 1 volume := by
  letI : IsFiniteMeasure (volume.restrict cc20RootDisplacementWindow) := by
    unfold cc20RootDisplacementWindow
    infer_instance
  rw [cc20FourierProjectionProfile,
    memLp_indicator_iff_restrict measurableSet_cc20RootDisplacementWindow]
  have hcont : Continuous (fun v : Real =>
      ((cc20RootLength⁻¹ : Real) : Complex) * cc20FourierPhase (-alpha) v) :=
    continuous_const.mul (continuous_cc20FourierPhase (-alpha))
  apply MemLp.of_bound hcont.aestronglyMeasurable cc20RootLength⁻¹
  filter_upwards with v
  rw [norm_mul, Complex.norm_real, norm_cc20FourierPhase, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr cc20RootLength_pos.le)]

theorem integrable_norm_cc20FourierProjectionProfile (alpha : Real) :
    Integrable (fun v => ‖cc20FourierProjectionProfile alpha v‖) volume := by
  exact ((memLp_one_iff_integrable.mp
    (memLp_one_cc20FourierProjectionProfile alpha)).norm)

/-- The two-variable integral kernel of `e_alpha`, before quotient lifting. -/
noncomputable def cc20FourierProjectionKernel (alpha : Real) :
    Real × Real -> Complex :=
  (cc20WindowPair cc20RootHalfWidth).indicator fun p =>
    ((cc20RootLength⁻¹ : Real) : Complex) *
      cc20FourierPhase alpha p.1 * star (cc20FourierPhase alpha p.2)

theorem memLp_cc20FourierProjectionKernel (alpha : Real) :
    MemLp (cc20FourierProjectionKernel alpha) 2 volume := by
  letI : IsFiniteMeasure
      (volume.restrict (cc20WindowPair cc20RootHalfWidth)) :=
    isFiniteMeasure_restrict.mpr
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  rw [cc20FourierProjectionKernel,
    memLp_indicator_iff_restrict (measurableSet_cc20WindowPair _)]
  have hcont : Continuous (fun p : Real × Real =>
      ((cc20RootLength⁻¹ : Real) : Complex) *
        cc20FourierPhase alpha p.1 * star (cc20FourierPhase alpha p.2)) :=
    (continuous_const.mul
      ((continuous_cc20FourierPhase alpha).comp continuous_fst)).mul
        ((continuous_cc20FourierPhase alpha).comp continuous_snd).star
  apply MemLp.of_bound hcont.aestronglyMeasurable cc20RootLength⁻¹
  filter_upwards with p
  rw [norm_mul, norm_mul, Complex.norm_real, norm_cc20FourierPhase, norm_star,
    norm_cc20FourierPhase, mul_one, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr cc20RootLength_pos.le)]

/-- Pointwise outer-product factorization of the projection kernel.  This is
the raw-function bridge from the square-window kernel to `rankOne`. -/
theorem cc20FourierProjectionKernel_eq_outerProduct
    (alpha : Real) (p : Real × Real) :
    cc20FourierProjectionKernel alpha p =
      cc20WindowFourierModeRaw alpha p.1 *
        (((cc20RootLength⁻¹ : Real) : Complex) *
          star (cc20WindowFourierModeRaw alpha p.2)) := by
  by_cases hx : p.1 ∈ cc20Window cc20RootHalfWidth
  · by_cases hy : p.2 ∈ cc20Window cc20RootHalfWidth
    · simp [cc20FourierProjectionKernel, cc20WindowFourierModeRaw,
        cc20WindowPair, hx, hy]
      ring
    · simp [cc20FourierProjectionKernel, cc20WindowFourierModeRaw,
        cc20WindowPair, hx, hy]
  · simp [cc20FourierProjectionKernel, cc20WindowFourierModeRaw,
      cc20WindowPair, hx]

theorem applyKernel_cc20FourierProjectionKernel
    (alpha : Real) (f : Real -> Complex) (x : Real) :
    applyKernel (cc20FourierProjectionKernel alpha) f x =
      cc20WindowFourierModeRaw alpha x *
        (((cc20RootLength⁻¹ : Real) : Complex) *
          ∫ y : Real, star (cc20WindowFourierModeRaw alpha y) * f y) := by
  unfold applyKernel
  calc
    (∫ y : Real, cc20FourierProjectionKernel alpha (x, y) * f y) =
        ∫ y : Real, (cc20WindowFourierModeRaw alpha x *
          ((cc20RootLength⁻¹ : Real) : Complex)) *
            (star (cc20WindowFourierModeRaw alpha y) * f y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [cc20FourierProjectionKernel_eq_outerProduct]
      ring
    _ = (cc20WindowFourierModeRaw alpha x *
          ((cc20RootLength⁻¹ : Real) : Complex)) *
            ∫ y : Real, star (cc20WindowFourierModeRaw alpha y) * f y := by
      rw [integral_const_mul]
    _ = _ := by ring

theorem integral_star_cc20WindowFourierModeRaw_mul
    (alpha : Real) (f : Lp Complex 2 (volume : Measure Real)) :
    (∫ y : Real, star (cc20WindowFourierModeRaw alpha y) * f y) =
      inner Complex (cc20WindowFourierVector alpha) f := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_cc20WindowFourierVector alpha] with y hy
  rw [hy]
  simp only [RCLike.inner_apply]
  exact mul_comm _ _

/-- Lifting the outer-product kernel to the `L2` quotient recovers exactly the
normalized rank-one Fourier projection. -/
theorem applyKernelLp_cc20FourierProjectionKernel_eq_projection
    (alpha : Real) :
    applyKernelLp (cc20FourierProjectionKernel alpha)
        (memLp_cc20FourierProjectionKernel alpha) =
      cc20FourierProjection alpha := by
  ext f
  have hleft :
      ((applyKernelLp (cc20FourierProjectionKernel alpha)
          (memLp_cc20FourierProjectionKernel alpha) f :
            Lp Complex 2 (volume : Measure Real)) : Real -> Complex) =ᵐ[volume]
        applyKernel (cc20FourierProjectionKernel alpha) f := by
    simpa only [applyKernelLp, applyKernelLpLinear] using
      (memLp_applyKernel_two (memLp_cc20FourierProjectionKernel alpha)
        (Lp.memLp f)).coeFn_toLp
  filter_upwards [hleft, coeFn_cc20WindowFourierVector alpha,
      Lp.coeFn_smul
        (inner Complex (cc20WindowFourierVector alpha) f)
        (cc20WindowFourierVector alpha),
      Lp.coeFn_smul ((cc20RootLength⁻¹ : Real) : Complex)
        ((inner Complex (cc20WindowFourierVector alpha) f) •
          cc20WindowFourierVector alpha)] with x hx hmode hinner hinv
  rw [hx, applyKernel_cc20FourierProjectionKernel,
    integral_star_cc20WindowFourierModeRaw_mul]
  simp only [cc20FourierProjection, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply]
  rw [hinv]
  simp only [Pi.smul_apply]
  rw [hinner]
  simp only [Pi.smul_apply, smul_eq_mul, hmode]
  ring

theorem sub_mem_cc20RootDisplacementWindow
    {x y : Real} (hx : x ∈ cc20Window cc20RootHalfWidth)
    (hy : y ∈ cc20Window cc20RootHalfWidth) :
    y - x ∈ cc20RootDisplacementWindow := by
  rw [cc20RootHalfWidth_eq_half_length] at hx hy
  change -(cc20RootLength / 2) ≤ x ∧ x ≤ cc20RootLength / 2 at hx
  change -(cc20RootLength / 2) ≤ y ∧ y ≤ cc20RootLength / 2 at hy
  change -cc20RootLength ≤ y - x ∧ y - x ≤ cc20RootLength
  constructor <;> linarith

/-- The rank-one projection kernel is exactly the square-window displacement
kernel of its equation-(118) profile. -/
theorem cc20FourierProjectionKernel_eq_windowedDisplacementKernel
    (alpha : Real) :
    cc20FourierProjectionKernel alpha =
      windowedDisplacementKernel (cc20FourierProjectionProfile alpha)
        cc20RootHalfWidth := by
  funext p
  by_cases hp : p ∈ cc20WindowPair cc20RootHalfWidth
  · have hv : p.2 - p.1 ∈ cc20RootDisplacementWindow :=
      sub_mem_cc20RootDisplacementWindow hp.1 hp.2
    rw [cc20FourierProjectionKernel, windowedDisplacementKernel,
      Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    rw [displacementKernel, cc20FourierProjectionProfile,
      Set.indicator_of_mem hv]
    rw [mul_assoc, cc20FourierPhase_mul_star]
  · rw [cc20FourierProjectionKernel, windowedDisplacementKernel,
      Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]

/-- Shared equation-(119) data.  The same finite index owns every frequency,
perturbed frequency, and coefficient used by both the operator and profile. -/
structure CC20FiniteRankData (ι : Type*) where
  lambda : Real
  frequency : ι -> Real
  perturbedFrequency : ι -> Real
  coefficient : ι -> Real

/-- One summand `e_n - d(n) e_{α_n}` of equation (119). -/
noncomputable def cc20FiniteRankOperatorTerm {ι : Type*}
    (data : CC20FiniteRankData ι) (i : ι) :
    Lp Complex 2 (volume : Measure Real) →L[Complex]
      Lp Complex 2 (volume : Measure Real) :=
  cc20FourierProjection (data.frequency i) -
    ((data.coefficient i : Real) : Complex) •
      cc20FourierProjection (data.perturbedFrequency i)

/-- The paper's finite-rank operator `T` from equation (119). -/
noncomputable def cc20FiniteRankOperator {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι) :
    Lp Complex 2 (volume : Measure Real) →L[Complex]
      Lp Complex 2 (volume : Measure Real) :=
  ((data.lambda : Real) : Complex) •
    ∑ i : ι, cc20FiniteRankOperatorTerm data i

/-- The displacement-profile summand paired with
`cc20FiniteRankOperatorTerm`. -/
noncomputable def cc20FiniteRankProfileTerm {ι : Type*}
    (data : CC20FiniteRankData ι) (i : ι) : Real -> Complex :=
  cc20FourierProjectionProfile (data.frequency i) -
    ((data.coefficient i : Real) : Complex) •
      cc20FourierProjectionProfile (data.perturbedFrequency i)

/-- The finite equation-(120) displacement profile `τ`. -/
noncomputable def cc20FiniteRankProfile {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι) : Real -> Complex :=
  ((data.lambda : Real) : Complex) •
    ∑ i : ι, cc20FiniteRankProfileTerm data i

theorem memLp_one_cc20FiniteRankProfileTerm {ι : Type*}
    (data : CC20FiniteRankData ι) (i : ι) :
    MemLp (cc20FiniteRankProfileTerm data i) 1 volume := by
  exact (memLp_one_cc20FourierProjectionProfile (data.frequency i)).sub
    ((memLp_one_cc20FourierProjectionProfile (data.perturbedFrequency i)).const_smul
      ((data.coefficient i : Real) : Complex))

theorem memLp_one_cc20FiniteRankProfile {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι) :
    MemLp (cc20FiniteRankProfile data) 1 volume := by
  unfold cc20FiniteRankProfile
  apply MemLp.const_smul
  exact memLp_finsetSum' Finset.univ fun i _ =>
    memLp_one_cc20FiniteRankProfileTerm data i

theorem integrable_norm_cc20FiniteRankProfile {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι) :
    Integrable (fun v => ‖cc20FiniteRankProfile data v‖) volume := by
  exact ((memLp_one_iff_integrable.mp
    (memLp_one_cc20FiniteRankProfile data)).norm)

/-- Equation (120): the finite-rank profile acts through the square-window
kernel as the displacement-first correlation integral. -/
theorem cc20FiniteRank_equation120 {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι) (eta xi : Real -> Complex)
    (heta : MemLp eta (ENNReal.ofReal 2))
    (hxi : MemLp xi (ENNReal.ofReal 2)) :
    (∫ x : Real, star (eta x) *
        applyKernel
          (windowedDisplacementKernel (cc20FiniteRankProfile data)
            cc20RootHalfWidth) xi x) =
      ∫ v : Real, cc20FiniteRankProfile data v *
        corrInnerSlice
          (cc20WindowZeroExtend cc20RootHalfWidth (fun x => star (eta x)))
          (cc20WindowZeroExtend cc20RootHalfWidth xi) v := by
  apply pairing_applyKernel_windowedDisplacementKernel_eq_weightedCorrFold
  exact integrable_displacementCorrelationIntegrand
    (memLp_one_cc20FiniteRankProfile data).1
    (integrable_norm_cc20FiniteRankProfile data)
    (memLp_cc20WindowZeroExtend cc20RootHalfWidth heta.star)
    (memLp_cc20WindowZeroExtend cc20RootHalfWidth hxi)


end C1CC20FiniteRankApproximation
end Source
end ConnesWeilRH
