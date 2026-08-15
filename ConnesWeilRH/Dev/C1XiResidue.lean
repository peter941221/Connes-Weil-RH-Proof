import ConnesWeilRH.Dev.C1XiLocalPrincipalPart
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# C1XiResidue - weighted local residues for Gate 2

This module will connect the local xi factorization to the single-weight
contour kernel.  It deliberately treats the weight continuity and the
principal-part calculation as separate facts, so a later contour proof cannot
silently use the total value of `logDeriv` at a zero.

No residue sum, rectangle identity, explicit formula, or RH claim is made.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiResidue

open Filter
open MeasureTheory
open CC20ZetaCounting
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiVerticalFunctional
open C1XiLocalPrincipalPart
open scoped Topology

/- The derivative of the Laplace kernel is still compactly supported in the
integration variable.  This lets the dominated parametric-integral theorem
produce a complex derivative without imposing any growth condition on `F`. -/
theorem hasDerivAt_laplaceAt
    (F : CompactLogTest) (s0 : Complex) :
    HasDerivAt
      (fun s : Complex => CC20YoshidaConvolution.CompactLogTest.laplaceAt F s)
      (∫ x : Real,
        (Complex.exp (s0 * (x : Complex)) * (x : Complex)) * F.test x)
      s0 := by
  obtain ⟨K, hK, hzero⟩ :=
    (exists_compact_iff_hasCompactSupport (f := F.test)).mpr F.compactSupport
  let integrand : Complex → Real → Complex := fun s x =>
    Complex.exp (s * (x : Complex)) * F.test x
  let integrandDeriv : Complex → Real → Complex := fun s x =>
    (Complex.exp (s * (x : Complex)) * (x : Complex)) * F.test x
  have hintegrand_continuous (s : Complex) : Continuous (integrand s) := by
    dsimp [integrand]
    exact
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).mul F.test.continuous
  have hintegrand_compact (s : Complex) : HasCompactSupport (integrand s) := by
    dsimp [integrand]
    exact F.compactSupport.mul_left
  have hderiv_continuous (s : Complex) : Continuous (integrandDeriv s) := by
    dsimp [integrandDeriv]
    exact
      ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).mul
          Complex.continuous_ofReal).mul F.test.continuous
  have hderiv_compact (s : Complex) : HasCompactSupport (integrandDeriv s) := by
    dsimp [integrandDeriv]
    exact F.compactSupport.mul_left
  let factor : Complex × Real → Complex := fun p =>
    Complex.exp (p.1 * (p.2 : Complex)) * (p.2 : Complex)
  have hfactor_continuous : Continuous factor := by
    dsimp [factor]
    exact
      (Complex.continuous_exp.comp
        (continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd))).mul
        (Complex.continuous_ofReal.comp continuous_snd)
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall s0 (1 : Real)).prod hK).exists_bound_of_continuousOn
      hfactor_continuous.continuousOn
  let bound : Real → Real := fun x => C * ‖F.test x‖
  have hbound_integrable : Integrable bound := by
    dsimp [bound]
    exact F.test.integrable.norm.const_mul C
  have hbound :
      ∀ᵐ x : Real ∂volume, ∀ s ∈ Metric.ball s0 1,
        ‖integrandDeriv s x‖ ≤ bound x := by
    filter_upwards with x
    intro s hs
    by_cases hxzero : F.test x = 0
    · simp [integrandDeriv, bound, hxzero]
    · have hxK : x ∈ K := by
        by_contra hxnot
        exact hxzero (hzero x hxnot)
      have hfactor : ‖factor (s, x)‖ ≤ C :=
        hC (s, x) ⟨Metric.ball_subset_closedBall hs, hxK⟩
      calc
        ‖integrandDeriv s x‖ = ‖factor (s, x)‖ * ‖F.test x‖ := by
          simp only [integrandDeriv, factor, norm_mul]
        _ ≤ C * ‖F.test x‖ :=
          mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
        _ = bound x := rfl
  have hpoint_deriv (x : Real) (s : Complex) :
      HasDerivAt (fun z : Complex => integrand z x) (integrandDeriv s x) s := by
    have hmul : HasDerivAt (fun z : Complex => z * (x : Complex))
        (x : Complex) s :=
      hasDerivAt_mul_const (x : Complex)
    simpa only [integrand, integrandDeriv] using hmul.cexp.mul_const (F.test x)
  have hmeas :
      ∀ᶠ s in 𝓝 s0, AEStronglyMeasurable (integrand s) volume :=
    Filter.Eventually.of_forall fun s =>
      (hintegrand_continuous s).aestronglyMeasurable
  have hderiv_meas : AEStronglyMeasurable (integrandDeriv s0) volume :=
    (hderiv_continuous s0).aestronglyMeasurable
  have hdiff :
      ∀ᵐ x : Real ∂volume, ∀ s ∈ Metric.ball s0 1,
        HasDerivAt (fun z => integrand z x) (integrandDeriv s x) s := by
    filter_upwards with x
    intro s hs
    exact hpoint_deriv x s
  have hparam :
      HasDerivAt (fun s : Complex => ∫ x : Real, integrand s x)
        (∫ x : Real, integrandDeriv s0 x) s0 :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Metric.ball s0 1)
      (Metric.ball_mem_nhds _ zero_lt_one)
      hmeas
      ((hintegrand_continuous s0).integrable_of_hasCompactSupport
        (hintegrand_compact s0))
      hderiv_meas
      hbound
      hbound_integrable
      hdiff).2
  have hintegral :
      (fun s : Complex => ∫ x : Real, integrand s x) =
        (fun s : Complex => CC20YoshidaConvolution.CompactLogTest.laplaceAt F s) := by
    funext s
    unfold CC20YoshidaConvolution.CompactLogTest.laplaceAt
    apply integral_congr_ae
    filter_upwards with x
    simp [integrand,
      CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply]
  rw [hintegral] at hparam
  simpa only [integrandDeriv] using hparam

theorem differentiable_laplaceAt (F : CompactLogTest) :
    Differentiable Complex
      (fun s : Complex => CC20YoshidaConvolution.CompactLogTest.laplaceAt F s) := by
  intro s
  exact (hasDerivAt_laplaceAt F s).differentiableAt

/-- The critical-line translation preserves holomorphy of the compact-log
Laplace weight.  This is the exact weight used in one spectral summand, rather
than an independently chosen contour test. -/
theorem differentiable_centeredLaplaceWeight (F : CompactLogTest) :
    Differentiable Complex (centeredLaplaceWeight F) := by
  unfold centeredLaplaceWeight
  exact (differentiable_laplaceAt F).comp
    (differentiable_id.sub (differentiable_const (1 / 2 : Complex)))

/- The compact-support witness lets us replace the whole-line integral by a
compact set integral.  The latter is continuous in the complex parameter by
the standard dominated parametric-integral theorem. -/
theorem continuous_laplaceAt (F : CompactLogTest) :
    Continuous (fun s : Complex =>
      CC20YoshidaConvolution.CompactLogTest.laplaceAt F s) := by
  obtain ⟨K, hK, hzero⟩ :=
    (exists_compact_iff_hasCompactSupport (f := F.test)).mpr F.compactSupport
  let integrand : Complex → Real → Complex := fun s x =>
    Complex.exp (s * (x : Complex)) * F.test x
  have hcont : Continuous (Function.uncurry integrand) := by
    change Continuous (fun p : Complex × Real =>
      Complex.exp (p.1 * (p.2 : Complex)) * F.test p.2)
    exact
      (Complex.continuous_exp.comp
        (continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd))).mul
        (F.test.continuous.comp continuous_snd)
  have hparam :
      Continuous (fun s : Complex => ∫ x in K, integrand s x) :=
    continuous_parametric_integral_of_continuous hcont hK
  have heq :
      (fun s : Complex => ∫ x in K, integrand s x) =
        (fun s : Complex =>
          CC20YoshidaConvolution.CompactLogTest.laplaceAt F s) := by
    funext s
    calc
      ∫ x in K, integrand s x = ∫ x, integrand s x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        simp [integrand, hzero x hx]
      _ = CC20YoshidaConvolution.CompactLogTest.laplaceAt F s := by
        unfold CC20YoshidaConvolution.CompactLogTest.laplaceAt
        apply integral_congr_ae
        filter_upwards with x
        simp [integrand,
          CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply]
  rw [← heq]
  exact hparam

theorem continuous_centeredLaplaceWeight (F : CompactLogTest) :
    Continuous (centeredLaplaceWeight F) := by
  unfold centeredLaplaceWeight
  exact (continuous_laplaceAt F).comp (continuous_id.sub continuous_const)

/-- A nonvanishing analytic cofactor has a continuous logarithmic derivative.
Keeping this as a local interface prevents a contour proof from treating the
total `logDeriv` value at a zero as its meromorphic value. -/
theorem continuousAt_logDeriv_of_analyticAt_of_ne_zero
    {h : Complex -> Complex} {s : Complex}
    (hanalytic : AnalyticAt Complex h s) (hnonzero : h s ≠ 0) :
    ContinuousAt (logDeriv h) s := by
  simpa only [logDeriv_apply] using
    hanalytic.deriv.continuousAt.div hanalytic.continuousAt hnonzero

/-- A nonvanishing analytic cofactor has a differentiable logarithmic
derivative on its zero-free local disc. -/
theorem differentiableAt_logDeriv_of_analyticAt_of_ne_zero
    {h : Complex -> Complex} {s : Complex}
    (hanalytic : AnalyticAt Complex h s) (hnonzero : h s ≠ 0) :
    DifferentiableAt Complex (logDeriv h) s := by
  simpa only [logDeriv_apply] using
    hanalytic.deriv.differentiableAt.div hanalytic.differentiableAt hnonzero

/-- Away from its zero set, the completed-xi logarithmic derivative is an
ordinary holomorphic function.  This is the regularity interface needed when
a later contour deletes small discs around finitely many zeros. -/
theorem differentiableAt_negativeXiLogDeriv_of_completedRiemannXi_ne_zero
    {s : Complex} (hs : completedRiemannXi s ≠ 0) :
    DifferentiableAt Complex negativeXiLogDeriv s := by
  unfold negativeXiLogDeriv
  exact
    (differentiableAt_logDeriv_of_analyticAt_of_ne_zero
      (differentiable_completedRiemannXi.analyticAt s) hs).neg

/-- The single-weight contour kernel is holomorphic away from the exact
completed-xi zero set.  Its only later exceptional points are therefore the
same source-indexed zeros whose local circles carry `spectralTerm`. -/
theorem differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero
    (F : CompactLogTest) {s : Complex} (hs : completedRiemannXi s ≠ 0) :
    DifferentiableAt Complex (xiContourKernel F) s := by
  unfold xiContourKernel
  exact
    (differentiableAt_negativeXiLogDeriv_of_completedRiemannXi_ne_zero hs).mul
      (differentiable_centeredLaplaceWeight F s)

theorem continuousAt_xiContourKernel_of_completedRiemannXi_ne_zero
    (F : CompactLogTest) {s : Complex} (hs : completedRiemannXi s ≠ 0) :
    ContinuousAt (xiContourKernel F) s :=
  (differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero F hs).continuousAt

/-- Multiplying the punctured xi logarithmic derivative by a continuous
weight turns the local principal part into its expected weighted residue.
The statement uses a single weight at `rho`; the later reflected right-line
kernel is not used here and therefore cannot double-count a xi zero. -/
theorem tendsto_weighted_negativeXiLogDeriv_at_xi_zero
    (rho : sourceNontrivialZeroSet) (W : Complex -> Complex)
    (hW : ContinuousAt W rho.1) :
    Tendsto
      (fun s => (s - rho.1) * (negativeXiLogDeriv s * W s))
      (𝓝[≠] rho.1)
      (𝓝 (-((xiMultiplicity rho : Complex) * W rho.1))) := by
  obtain ⟨h, hanalytic, hnonzero, hlocal⟩ :=
    exists_negativeXiLogDeriv_local_principal_part rho
  have hdelta : Tendsto (fun s : Complex => s - rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    have hdeltaAt :
        Tendsto (fun s : Complex => s - rho.1) (𝓝 rho.1)
          (𝓝 (rho.1 - rho.1)) :=
      tendsto_id.sub_const rho.1
    simpa using hdeltaAt.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (logDeriv h) (𝓝[≠] rho.1) (𝓝 (logDeriv h rho.1)) := by
    simpa only [logDeriv_apply] using
      ((hanalytic.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div
        (hanalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hnonzero)
  have hcorrection :
      Tendsto (fun s : Complex => (s - rho.1) * logDeriv h s)
        (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using hdelta.mul hlog
  have hregular :
      Tendsto
        (fun s : Complex =>
          (-((xiMultiplicity rho : Complex)) - (s - rho.1) * logDeriv h s) * W s)
        (𝓝[≠] rho.1)
        (𝓝 (-((xiMultiplicity rho : Complex) * W rho.1))) := by
    have hweight : Tendsto W (𝓝[≠] rho.1) (𝓝 (W rho.1)) :=
      hW.tendsto.mono_left nhdsWithin_le_nhds
    convert (tendsto_const_nhds.sub hcorrection).mul hweight using 1 <;> ring
  apply hregular.congr'
  filter_upwards [hlocal, self_mem_nhdsWithin] with s hs hne
  have hsne : s - rho.1 ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
  rw [hs]
  field_simp [hsne]

/-- The single-weight contour kernel has one copy of the expected xi-zero
residue.  In particular, the local contour contribution matches
`spectralTerm F rho` up to the orientation sign supplied by
`negativeXiLogDeriv`. -/
theorem tendsto_xiContourKernel_at_xi_zero
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    Tendsto
      (fun s => (s - rho.1) * xiContourKernel F s)
      (𝓝[≠] rho.1)
      (𝓝 (-spectralTerm F rho)) := by
  have hweight : ContinuousAt (centeredLaplaceWeight F) rho.1 :=
    (continuous_centeredLaplaceWeight F).continuousAt
  simpa only [xiContourKernel,
    spectralTerm_eq_multiplicity_mul_centeredLaplaceWeight] using
    tendsto_weighted_negativeXiLogDeriv_at_xi_zero rho
      (centeredLaplaceWeight F) hweight

/-- Around each xi zero, one local cofactor supplies a positive safe radius.
Every positive circle no larger than that radius has the expected contribution;
this stronger form is needed when a later finite contour chooses pairwise
disjoint circles. -/
theorem exists_safeCircleRadius_xiContourKernel_eq_neg_residue
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    ∃ Rmax : Real, 0 < Rmax ∧ ∀ R : Real, 0 < R → R ≤ Rmax →
      (∮ s in C(rho.1, R), xiContourKernel F s) =
        -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
  obtain ⟨h, hanalytic, hnonzero, hlocal⟩ :=
    exists_negativeXiLogDeriv_local_principal_part rho
  obtain ⟨Ranalytic, hRanalytic, hanalyticOn⟩ :=
    hanalytic.exists_ball_analyticOnNhd
  have hnonzeroEventually : ∀ᶠ s in 𝓝 rho.1, h s ≠ 0 :=
    (hanalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hnonzero
  obtain ⟨Rnonzero, hRnonzero, hnonzeroOn⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp hnonzeroEventually
  obtain ⟨Rlocal, hRlocal, hlocalOn⟩ :=
    (nhdsWithin_hasBasis Metric.nhds_basis_closedBall _).mem_iff.mp hlocal
  let Rmax : Real := min Rlocal (min Ranalytic Rnonzero) / 2
  have hRmaxmin : 0 < min Rlocal (min Ranalytic Rnonzero) :=
    lt_min hRlocal (lt_min hRanalytic hRnonzero)
  have hRmax : 0 < Rmax := by
    dsimp [Rmax]
    exact half_pos hRmaxmin
  have hRmaxltMin : Rmax < min Rlocal (min Ranalytic Rnonzero) := by
    dsimp [Rmax]
    linarith
  have hRmaxleLocal : Rmax ≤ Rlocal :=
    hRmaxltMin.le.trans (min_le_left _ _)
  have hRmaxltAnalytic : Rmax < Ranalytic :=
    hRmaxltMin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hRmaxleNonzero : Rmax ≤ Rnonzero :=
    hRmaxltMin.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨Rmax, hRmax, ?_⟩
  intro R hR hRle
  have hRleLocal : R ≤ Rlocal := hRle.trans hRmaxleLocal
  have hRltAnalytic : R < Ranalytic := hRle.trans_lt hRmaxltAnalytic
  have hRleNonzero : R ≤ Rnonzero := hRle.trans hRmaxleNonzero
  let regular : Complex -> Complex := fun s =>
    (-((xiMultiplicity rho : Complex)) - (s - rho.1) * logDeriv h s) *
      centeredLaplaceWeight F s
  have hregular_center : regular rho.1 = -spectralTerm F rho := by
    simp only [regular, sub_self, zero_mul, sub_zero]
    rw [spectralTerm_eq_multiplicity_mul_centeredLaplaceWeight]
    ring
  have hregular_continuous : ContinuousOn regular (Metric.closedBall rho.1 R) := by
    intro s hs
    have hsAnalyticBall : s ∈ Metric.ball rho.1 Ranalytic := by
      rw [Metric.mem_ball]
      rw [Metric.mem_closedBall] at hs
      exact lt_of_le_of_lt hs hRltAnalytic
    have hsNonzeroBall : s ∈ Metric.closedBall rho.1 Rnonzero := by
      rw [Metric.mem_closedBall]
      rw [Metric.mem_closedBall] at hs
      exact hs.trans hRleNonzero
    have hlog : ContinuousAt (logDeriv h) s :=
      continuousAt_logDeriv_of_analyticAt_of_ne_zero
        (hanalyticOn s hsAnalyticBall) (hnonzeroOn hsNonzeroBall)
    have hcore : ContinuousAt
        (fun z : Complex =>
          -((xiMultiplicity rho : Complex)) - (z - rho.1) * logDeriv h z) s := by
      exact continuousAt_const.sub
        ((continuousAt_id.sub continuousAt_const).mul hlog)
    exact (hcore.mul (continuous_centeredLaplaceWeight F).continuousAt).continuousWithinAt
  have hregular_differentiable :
      ∀ s ∈ Metric.ball rho.1 R, DifferentiableAt Complex regular s := by
    intro s hs
    have hsAnalyticBall : s ∈ Metric.ball rho.1 Ranalytic := by
      rw [Metric.mem_ball] at hs ⊢
      exact lt_trans hs hRltAnalytic
    have hsNonzeroBall : s ∈ Metric.closedBall rho.1 Rnonzero := by
      rw [Metric.mem_closedBall]
      rw [Metric.mem_ball] at hs
      exact hs.le.trans hRleNonzero
    have hlog : DifferentiableAt Complex (logDeriv h) s :=
      differentiableAt_logDeriv_of_analyticAt_of_ne_zero
        (hanalyticOn s hsAnalyticBall) (hnonzeroOn hsNonzeroBall)
    have hcore : DifferentiableAt Complex
        (fun z : Complex =>
          -((xiMultiplicity rho : Complex)) - (z - rho.1) * logDeriv h z) s := by
      exact
        (differentiable_const (c := -((xiMultiplicity rho : Complex))).differentiableAt).sub
          ((differentiableAt_id.sub
            (differentiable_const (c := rho.1)).differentiableAt).mul hlog)
    exact hcore.mul (differentiable_centeredLaplaceWeight F s)
  have hcircle_regular :
      (∮ s in C(rho.1, R), (s - rho.1)⁻¹ • regular s) =
        (2 * (Real.pi : Complex) * Complex.I) • regular rho.1 := by
    apply Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      hR (s := (∅ : Set Complex)) Set.countable_empty hregular_continuous
    intro s hs
    exact hregular_differentiable s hs.1
  have hcircle_regular_value :
      (∮ s in C(rho.1, R), (s - rho.1)⁻¹ • regular s) =
        -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
    rw [hregular_center] at hcircle_regular
    simpa only [smul_eq_mul, mul_neg, neg_mul] using hcircle_regular
  calc
    (∮ s in C(rho.1, R), xiContourKernel F s) =
        ∮ s in C(rho.1, R),
          (s - rho.1)⁻¹ • (s - rho.1) • xiContourKernel F s :=
      (circleIntegral.integral_sub_inv_smul_sub_smul
        (xiContourKernel F) rho.1 rho.1 R).symm
    _ = ∮ s in C(rho.1, R), (s - rho.1)⁻¹ • regular s := by
      apply circleIntegral.integral_congr hR.le
      intro s hs
      have hsClosed : s ∈ Metric.closedBall rho.1 R :=
        Metric.sphere_subset_closedBall hs
      have hsLocal : s ∈ Metric.closedBall rho.1 Rlocal := by
        rw [Metric.mem_closedBall] at hsClosed ⊢
        exact hsClosed.trans hRleLocal
      have hsne : s ≠ rho.1 := by
        intro hsr
        subst s
        have hszero : (0 : Real) = R := by
          simpa only [Metric.mem_sphere, dist_self] using hs
        exact hR.ne' hszero.symm
      have hprincipal := hlocalOn ⟨hsLocal, by simpa using hsne⟩
      have hregular : (s - rho.1) • xiContourKernel F s = regular s := by
        rw [smul_eq_mul, xiContourKernel, hprincipal]
        dsimp only [regular]
        field_simp [sub_ne_zero.mpr hsne]
      change (s - rho.1)⁻¹ • ((s - rho.1) • xiContourKernel F s) =
        (s - rho.1)⁻¹ • regular s
      rw [hregular]
    _ = -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) :=
      hcircle_regular_value

/-- Existential small-circle form of the local xi residue.  The chosen radius
is the safe radius supplied by
`exists_safeCircleRadius_xiContourKernel_eq_neg_residue`. -/
theorem exists_circleIntegral_xiContourKernel_eq_neg_residue
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    ∃ R : Real, 0 < R ∧
      (∮ s in C(rho.1, R), xiContourKernel F s) =
        -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
  obtain ⟨R, hR, hcircle⟩ :=
    exists_safeCircleRadius_xiContourKernel_eq_neg_residue F rho
  exact ⟨R, hR, hcircle R hR le_rfl⟩

end C1XiResidue
end Source
end ConnesWeilRH
