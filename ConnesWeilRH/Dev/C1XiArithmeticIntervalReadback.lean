import ConnesWeilRH.Dev.C1XiArithmeticRightLine
import ConnesWeilRH.Dev.C1XiResidue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# C1XiArithmeticIntervalReadback - finite-height arithmetic readback

This module keeps the arithmetic right-line argument inside its honest
absolute-convergence region.  For `1 < c`, the von Mangoldt L-series is
expanded pointwise and then integrated term by term on a finite height
interval.  The domination is explicit: the compact test weight is bounded on
the interval, while the remaining coefficient sequence is the absolute
convergent L-series at the real point `c`.

The pole and Gamma_R pieces are handled as continuous finite-height terms.  A
finite prime-power truncation is continuous as `c -> 1+`; the boundary value
of the full von Mangoldt series is deliberately left as a data-bearing
contract, since absolute convergence at `Re(s) > 1` does not imply a boundary
limit on `Re(s) = 1`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiArithmeticIntervalReadback

open MeasureTheory
open Set
open Filter
open Complex
open CC20ZetaCounting
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1XiArithmeticRightLine
open C1XiResidue
open C1XiVerticalFunctional
open scoped BigOperators Interval LSeries.notation Topology

noncomputable section

private def vonMangoldtSequence : Nat → Complex :=
  fun n => (ArithmeticFunction.vonMangoldt n : Complex)

/-- One prime-power term of the arithmetic part on the oriented right line. -/
noncomputable def arithmeticPrimePowerIntegrand
    (F : CompactLogTest) (c t : Real) (n : Nat) : Complex :=
  LSeries.term vonMangoldtSequence (verticalPoint c t) n *
      symmetrizedLaplaceWeight F (verticalPoint c t) * Complex.I

/-- The full von Mangoldt contribution before it is expanded into terms. -/
noncomputable def arithmeticLSeriesIntegrand
    (F : CompactLogTest) (c t : Real) : Complex :=
  vonMangoldtLSeries (verticalPoint c t) *
      symmetrizedLaplaceWeight F (verticalPoint c t) * Complex.I

/-- The two elementary pole factors in the same oriented normalization. -/
noncomputable def elementaryPoleIntegrand
    (F : CompactLogTest) (c t : Real) : Complex :=
  -(1 / verticalPoint c t + 1 / (verticalPoint c t - 1)) *
      symmetrizedLaplaceWeight F (verticalPoint c t) * Complex.I

/-- The Gamma_R contribution in the same oriented normalization. -/
noncomputable def gammaRIntegrand
    (F : CompactLogTest) (c t : Real) : Complex :=
  -logDeriv Complex.Gammaℝ (verticalPoint c t) *
      symmetrizedLaplaceWeight F (verticalPoint c t) * Complex.I

private theorem differentiableAt_GammaR_of_pos_re
    {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex Complex.Gammaℝ s := by
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hinv : DifferentiableAt Complex
      (fun z : Complex => (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have h := hinv.inv (inv_ne_zero hgamma)
  change DifferentiableAt Complex
    (fun z : Complex => ((Complex.Gammaℝ z)⁻¹)⁻¹) s at h
  simpa only [inv_inv] using h

private theorem continuous_verticalPoint (c : Real) :
    Continuous (fun t : Real => verticalPoint c t) := by
  unfold verticalPoint
  fun_prop

private theorem continuous_symmetrizedWeight_vertical
    (F : CompactLogTest) (c : Real) :
    Continuous (fun t : Real =>
      symmetrizedLaplaceWeight F (verticalPoint c t)) := by
  unfold symmetrizedLaplaceWeight
  apply Continuous.add
  · exact (continuous_centeredLaplaceWeight F).comp
      (continuous_verticalPoint c)
  · apply (continuous_centeredLaplaceWeight F).comp
    have h : Continuous (fun t : Real => 1 - verticalPoint c t) :=
      continuous_const.sub (continuous_verticalPoint c)
    exact h

private theorem continuous_lSeriesTerm_vertical
    {f : Nat → Complex} {c : Real} (n : Nat) (hn : n ≠ 0) :
    Continuous (fun t : Real => LSeries.term f (verticalPoint c t) n) := by
  rw [funext (fun t => LSeries.term_of_ne_zero hn f (verticalPoint c t))]
  have hpoint := continuous_verticalPoint c
  have hncomplex : (n : Complex) ≠ 0 := by
    exact_mod_cast hn
  have hpow : Continuous (fun t : Real =>
      (n : Complex) ^ verticalPoint c t) :=
    hpoint.const_cpow (Or.inl hncomplex)
  have hpow_ne : ∀ t : Real, (n : Complex) ^ verticalPoint c t ≠ 0 := by
    intro t
    exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hncomplex))
  exact continuous_const.div hpow hpow_ne

private theorem norm_lSeriesTerm_vertical_eq_real
    {f : Nat → Complex} (c t : Real) (n : Nat) :
    ‖LSeries.term f (verticalPoint c t) n‖ =
      ‖LSeries.term f (c : Complex) n‖ := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [LSeries.norm_term_eq, verticalPoint, hn, ↓reduceIte]
    congr 2
    simp

private theorem hasSum_arithmeticPrimePowerIntegrand
    (F : CompactLogTest) {c t : Real} (hc : 1 < c) :
    HasSum (fun n : Nat => arithmeticPrimePowerIntegrand F c t n)
      (arithmeticLSeriesIntegrand F c t) := by
  have hseries : HasSum
      (fun n : Nat => LSeries.term vonMangoldtSequence
        (verticalPoint c t) n)
      (vonMangoldtLSeries (verticalPoint c t)) := by
    unfold vonMangoldtLSeries
    exact (ArithmeticFunction.LSeriesSummable_vonMangoldt (by
      simpa [verticalPoint] using hc)).hasSum
  simpa only [arithmeticPrimePowerIntegrand, arithmeticLSeriesIntegrand] using
    (hseries.mul_right
      (symmetrizedLaplaceWeight F (verticalPoint c t))).mul_right Complex.I

private theorem intervalIntegrable_arithmeticPrimePowerIntegrand
    (F : CompactLogTest) (c T : Real) (n : Nat) :
    IntervalIntegrable (fun t : Real =>
      arithmeticPrimePowerIntegrand F c t n) volume (-T) T := by
  by_cases hn : n = 0
  · simp [arithmeticPrimePowerIntegrand, hn]
  · have hterm := continuous_lSeriesTerm_vertical (f := vonMangoldtSequence)
      (c := c) n hn
    have hweight := continuous_symmetrizedWeight_vertical F c
    exact (hterm.mul hweight).mul continuous_const |>.intervalIntegrable _ _

private theorem intervalIntegrable_elementaryPoleIntegrand
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    IntervalIntegrable (fun t : Real => elementaryPoleIntegrand F c t)
      volume (-T) T := by
  have hpoint := continuous_verticalPoint c
  have hzero : ∀ t : Real, verticalPoint c t ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [verticalPoint] at hre
    linarith
  have hone : ∀ t : Real, verticalPoint c t - 1 ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [verticalPoint] at hre
    linarith
  have hfirst : Continuous (fun t : Real => 1 / verticalPoint c t) :=
    continuous_const.div hpoint hzero
  have hsecond : Continuous (fun t : Real =>
      1 / (verticalPoint c t - 1)) := by
    apply continuous_const.div
    · exact hpoint.sub continuous_const
    · exact hone
  have hweight := continuous_symmetrizedWeight_vertical F c
  exact ((hfirst.add hsecond).neg.mul hweight).mul continuous_const |>.intervalIntegrable _ _

private theorem analyticAt_GammaR_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    AnalyticAt Complex Complex.Gammaℝ s := by
  apply DifferentiableOn.analyticAt (s := {z : Complex | 1 < z.re})
  · intro z hz
    have hz' : 1 < z.re := hz
    exact (differentiableAt_GammaR_of_pos_re (by linarith [hz'])).differentiableWithinAt
  · exact (isOpen_lt continuous_const continuous_re).mem_nhds hs

private theorem continuous_logDeriv_GammaR_vertical
    {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real =>
      logDeriv Complex.Gammaℝ (verticalPoint c t)) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hlog : ContinuousAt (logDeriv Complex.Gammaℝ) (verticalPoint c t) :=
    continuousAt_logDeriv_of_analyticAt_of_ne_zero
      (analyticAt_GammaR_of_one_lt_re (s := verticalPoint c t) (by
        simp [verticalPoint]
        exact hc))
      (Complex.Gammaℝ_ne_zero_of_re_pos (by
        simp [verticalPoint]
        linarith [hc]))
  simpa only [Function.comp_apply] using
    hlog.comp' (f := fun t : Real => verticalPoint c t) (x := t)
      (continuous_verticalPoint c).continuousAt

private theorem intervalIntegrable_gammaRIntegrand
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    IntervalIntegrable (fun t : Real => gammaRIntegrand F c t) volume (-T) T := by
  have hgamma := continuous_logDeriv_GammaR_vertical hc
  have hweight := continuous_symmetrizedWeight_vertical F c
  exact (hgamma.neg.mul hweight).mul continuous_const |>.intervalIntegrable _ _

private theorem analyticAt_GammaR_of_pos_re
    {s : Complex} (hs : 0 < s.re) :
    AnalyticAt Complex Complex.Gammaℝ s := by
  apply DifferentiableOn.analyticAt (s := {z : Complex | 0 < z.re})
  · intro z hz
    exact (differentiableAt_GammaR_of_pos_re hz).differentiableWithinAt
  · exact (isOpen_lt continuous_const continuous_re).mem_nhds hs

private theorem continuous_positive_verticalPoint :
    Continuous (fun p : {c : Real // 0 < c} × Real =>
      verticalPoint p.1.1 p.2) := by
  unfold verticalPoint
  fun_prop

private theorem continuous_logDeriv_GammaR_positive_vertical :
    Continuous (fun p : {c : Real // 0 < c} × Real =>
      logDeriv Complex.Gammaℝ (verticalPoint p.1.1 p.2)) := by
  apply continuous_iff_continuousAt.2
  intro p
  have hlog : ContinuousAt (logDeriv Complex.Gammaℝ)
      (verticalPoint p.1.1 p.2) :=
    continuousAt_logDeriv_of_analyticAt_of_ne_zero
      (analyticAt_GammaR_of_pos_re (s := verticalPoint p.1.1 p.2) (by
        simp [verticalPoint]
        exact p.1.2))
      (Complex.Gammaℝ_ne_zero_of_re_pos (by
        simp [verticalPoint]
        exact p.1.2))
  simpa only [Function.comp_apply] using
    hlog.comp' (f := fun q : {c : Real // 0 < c} × Real =>
      verticalPoint q.1.1 q.2) (x := p)
      continuous_positive_verticalPoint.continuousAt

private theorem continuous_symmetrizedWeight_positive_vertical
    (F : CompactLogTest) :
    Continuous (fun p : {c : Real // 0 < c} × Real =>
      symmetrizedLaplaceWeight F (verticalPoint p.1.1 p.2)) := by
  unfold symmetrizedLaplaceWeight
  apply Continuous.add
  · exact (continuous_centeredLaplaceWeight F).comp
      continuous_positive_verticalPoint
  · exact (continuous_centeredLaplaceWeight F).comp
      (continuous_const.sub continuous_positive_verticalPoint)

private theorem continuous_gammaRIntegrand_positive_vertical
    (F : CompactLogTest) :
    Continuous (fun p : {c : Real // 0 < c} × Real =>
      gammaRIntegrand F p.1.1 p.2) := by
  unfold gammaRIntegrand
  exact (continuous_logDeriv_GammaR_positive_vertical.neg.mul
    (continuous_symmetrizedWeight_positive_vertical F)).mul continuous_const

theorem continuous_gammaRIntegrand_intervalIntegral
    (F : CompactLogTest) (T : Real) :
    Continuous (fun c : {c : Real // 0 < c} =>
      ∫ t : Real in (-T)..T, gammaRIntegrand F c t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · simpa only [Function.uncurry] using
      (continuous_gammaRIntegrand_positive_vertical F)
  · exact continuous_const

theorem tendsto_gammaRIntegrand_intervalIntegral_c_to_one
    (F : CompactLogTest) (T : Real) :
    Tendsto
      (fun c : Real =>
        ∫ t : Real in (-T)..T, gammaRIntegrand F c t)
      (𝓝[>] (1 : Real))
      (𝓝 (∫ t : Real in (-T)..T, gammaRIntegrand F 1 t)) := by
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
        ∫ t : Real in (-T)..T, gammaRIntegrand F (liftC c) t)
      (𝓝[>] (1 : Real))
      (𝓝 (∫ t : Real in (-T)..T,
        gammaRIntegrand F (⟨1, by norm_num⟩ : {c : Real // 0 < c}) t)) := by
    simpa only [Function.comp_apply] using
      ((continuous_gammaRIntegrand_intervalIntegral F T).continuousAt.tendsto.comp
        hlift)
  have heq :
      (fun c : Real =>
        ∫ t : Real in (-T)..T, gammaRIntegrand F (liftC c) t) =ᶠ[𝓝[>] (1 : Real)]
      (fun c : Real =>
        ∫ t : Real in (-T)..T, gammaRIntegrand F c t) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc' : 1 < c := hc
    have hcmax : max c (1 / 2 : Real) = c := by
      exact max_eq_left (by linarith [hc'])
    simp only [liftC]
    rw [hcmax]
  simpa using hcont.congr' heq

private theorem continuous_negativeXiLogDeriv_vertical
    {c : Real} (hc : 1 < c) :
    Continuous (fun t : Real => negativeXiLogDeriv (verticalPoint c t)) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hxi : completedRiemannXi (verticalPoint c t) ≠ 0 :=
    completedRiemannXi_ne_zero_of_one_le_re (by
      simp [verticalPoint]
      linarith [hc])
  simpa only [Function.comp_apply] using
    (differentiableAt_negativeXiLogDeriv_of_completedRiemannXi_ne_zero hxi).continuousAt.comp'
      (f := fun t : Real => verticalPoint c t) (x := t)
      (continuous_verticalPoint c).continuousAt

private theorem intervalIntegrable_verticalIntegrand
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    IntervalIntegrable (fun t : Real => verticalIntegrand F c t) volume (-T) T := by
  have hnegative := continuous_negativeXiLogDeriv_vertical hc
  have hweight := continuous_symmetrizedWeight_vertical F c
  exact (hnegative.mul hweight).mul continuous_const |>.intervalIntegrable _ _

theorem verticalIntegrand_eq_arithmetic_components
    (F : CompactLogTest) {c t : Real} (hc : 1 < c) :
    verticalIntegrand F c t =
      elementaryPoleIntegrand F c t + gammaRIntegrand F c t +
        arithmeticLSeriesIntegrand F c t := by
  rw [verticalIntegrand, xiRightLineKernel,
    negativeXiLogDeriv_eq_vonMangoldtLSeries_add_GammaR
      (by simpa [verticalPoint] using hc)]
  simp only [elementaryPoleIntegrand, gammaRIntegrand,
    arithmeticLSeriesIntegrand, symmetrizedLaplaceWeight]
  ring

theorem hasSum_intervalIntegral_arithmeticPrimePowerIntegrand
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    HasSum
      (fun n : Nat => ∫ t : Real in (-T)..T,
        arithmeticPrimePowerIntegrand F c t n)
      (∫ t : Real in (-T)..T, arithmeticLSeriesIntegrand F c t) := by
  have hseries := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : Complex))
    (by simpa using hc)
  obtain ⟨M₀, hM₀⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (continuous_symmetrizedWeight_vertical F c).continuousOn
  let M : Real := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have hM : ∀ t ∈ [[-T, T]],
      ‖symmetrizedLaplaceWeight F (verticalPoint c t)‖ ≤ M := by
    intro t ht
    exact (hM₀ t ht).trans (le_max_left _ _)
  let bound : Nat → Real → Real := fun n _ =>
    M * ‖LSeries.term vonMangoldtSequence (c : Complex) n‖
  have hF_meas : ∀ n : Nat, AEStronglyMeasurable
      (fun t : Real => arithmeticPrimePowerIntegrand F c t n)
      (volume.restrict (uIoc (-T) T)) := by
    intro n
    by_cases hn : n = 0
    · simpa [arithmeticPrimePowerIntegrand, hn] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : Real => (0 : Complex))
            (volume.restrict (uIoc (-T) T)))
    · exact (continuous_lSeriesTerm_vertical (f := vonMangoldtSequence) n hn).mul
        (continuous_symmetrizedWeight_vertical F c) |>.mul continuous_const |>
          Continuous.aestronglyMeasurable
  have hbound : ∀ n : Nat, ∀ᵐ t : Real ∂volume,
      t ∈ uIoc (-T) T →
        ‖arithmeticPrimePowerIntegrand F c t n‖ ≤ bound n t := by
    intro n
    filter_upwards with t ht
    have htcc : t ∈ [[-T, T]] := uIoc_subset_uIcc ht
    rw [arithmeticPrimePowerIntegrand, norm_mul, norm_mul, norm_I,
      mul_one, norm_lSeriesTerm_vertical_eq_real]
    simpa [bound, mul_comm] using
      (mul_le_mul_of_nonneg_left (hM t htcc)
        (norm_nonneg (LSeries.term vonMangoldtSequence (c : Complex) n)))
  have hbound_summable : ∀ᵐ t : Real ∂volume,
      t ∈ uIoc (-T) T → Summable (fun n => bound n t) := by
    filter_upwards with t ht
    dsimp [bound]
    exact hseries.norm.mul_left M
  have hbound_integrable : IntervalIntegrable
      (fun t : Real => ∑' n, bound n t) volume (-T) T := by
    have hconstant : IntervalIntegrable (fun _ : Real =>
        M * ∑' n, ‖LSeries.term vonMangoldtSequence (c : Complex) n‖)
        volume (-T) T := intervalIntegrable_const
    simpa only [bound, tsum_mul_left] using hconstant
  have hlim : ∀ᵐ t : Real ∂volume,
      t ∈ uIoc (-T) T → HasSum
        (fun n : Nat => arithmeticPrimePowerIntegrand F c t n)
        (arithmeticLSeriesIntegrand F c t) := by
    filter_upwards with t ht
    exact hasSum_arithmeticPrimePowerIntegrand F (by simpa [verticalPoint] using hc)
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := bound) hF_meas hbound hbound_summable hbound_integrable hlim

theorem tsum_intervalIntegral_arithmeticPrimePowerIntegrand_eq
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    (∑' n : Nat, ∫ t : Real in (-T)..T,
      arithmeticPrimePowerIntegrand F c t n) =
      ∫ t : Real in (-T)..T, arithmeticLSeriesIntegrand F c t := by
  exact (hasSum_intervalIntegral_arithmeticPrimePowerIntegrand F hc).tsum_eq

theorem intervalIntegrable_arithmeticLSeriesIntegrand_of_components
    (F : CompactLogTest) {c T : Real} (hc : 1 < c) :
    IntervalIntegrable (fun t : Real =>
      verticalIntegrand F c t - elementaryPoleIntegrand F c t -
        gammaRIntegrand F c t) volume (-T) T := by
  rw [show (fun t : Real =>
      verticalIntegrand F c t - elementaryPoleIntegrand F c t -
        gammaRIntegrand F c t) =
      fun t => arithmeticLSeriesIntegrand F c t by
        funext t
        rw [verticalIntegrand_eq_arithmetic_components F hc]
        ring]
  have hcomponents : IntervalIntegrable (fun t : Real =>
      verticalIntegrand F c t - elementaryPoleIntegrand F c t -
        gammaRIntegrand F c t) volume (-T) T :=
    ((intervalIntegrable_verticalIntegrand F (c := c) (T := T) hc).sub
      (intervalIntegrable_elementaryPoleIntegrand F (c := c) (T := T) hc)).sub
        (intervalIntegrable_gammaRIntegrand F (c := c) (T := T) hc)
  have harithmetic : IntervalIntegrable (fun t : Real =>
      arithmeticLSeriesIntegrand F c t) volume (-T) T := by
    rw [← show (fun t : Real =>
        verticalIntegrand F c t - elementaryPoleIntegrand F c t -
          gammaRIntegrand F c t) =
      fun t => arithmeticLSeriesIntegrand F c t by
        funext t
        rw [verticalIntegrand_eq_arithmetic_components F hc]
        ring]
    exact hcomponents
  exact harithmetic

/-- A finite prime-power truncation used for the `c -> 1+` boundary step. -/
noncomputable def finiteArithmeticPrimePowerIntegrand
    (F : CompactLogTest) (N : Nat) (c t : Real) : Complex :=
  (∑ n ∈ Finset.range (N + 1),
      LSeries.term vonMangoldtSequence (verticalPoint c t) n) *
    symmetrizedLaplaceWeight F (verticalPoint c t) * Complex.I

theorem continuous_finiteArithmeticPrimePowerIntegrand
    (F : CompactLogTest) (N : Nat) :
    Continuous (fun p : Real × Real =>
      finiteArithmeticPrimePowerIntegrand F N p.1 p.2) := by
  unfold finiteArithmeticPrimePowerIntegrand
  have hpoint : Continuous (fun p : Real × Real => verticalPoint p.1 p.2) := by
    unfold verticalPoint
    fun_prop
  have hsum : Continuous (fun p : Real × Real =>
      ∑ n ∈ Finset.range (N + 1),
        LSeries.term vonMangoldtSequence
          (verticalPoint p.1 p.2) n) := by
    apply continuous_finsetSum
    intro n hn
    by_cases hn0 : n = 0
    · simpa [hn0] using
        (continuous_const : Continuous (fun _ : Real × Real => (0 : Complex)))
    · have hncomplex : (n : Complex) ≠ 0 := by
        exact_mod_cast hn0
      have hpow : Continuous (fun p : Real × Real =>
          (n : Complex) ^ verticalPoint p.1 p.2) :=
        hpoint.const_cpow (Or.inl hncomplex)
      have hpow_ne : ∀ p : Real × Real,
          (n : Complex) ^ verticalPoint p.1 p.2 ≠ 0 := by
        intro p
        exact Complex.cpow_ne_zero_iff.mpr (Or.inl hncomplex)
      simpa only [LSeries.term_of_ne_zero hn0] using
        (continuous_const.div hpow hpow_ne)
  have hweight : Continuous (fun p : Real × Real =>
      symmetrizedLaplaceWeight F (verticalPoint p.1 p.2)) := by
    unfold symmetrizedLaplaceWeight
    apply Continuous.add
    · exact (continuous_centeredLaplaceWeight F).comp hpoint
    · exact (continuous_centeredLaplaceWeight F).comp
        (continuous_const.sub hpoint)
  exact (hsum.mul hweight).mul continuous_const

theorem tendsto_finiteArithmeticPrimePowerIntegrand_c_to_one
    (F : CompactLogTest) (N : Nat) (t : Real) :
    Tendsto (fun c : Real => finiteArithmeticPrimePowerIntegrand F N c t)
      (𝓝[>] (1 : Real))
      (𝓝 (finiteArithmeticPrimePowerIntegrand F N 1 t)) := by
  have hpair : ContinuousAt (fun c : Real => (c, t)) 1 :=
    continuousAt_id.prodMk continuousAt_const
  have hcont : ContinuousAt
      (fun c : Real => finiteArithmeticPrimePowerIntegrand F N c t) 1 := by
    simpa only [Function.comp_apply] using
      (continuous_finiteArithmeticPrimePowerIntegrand F N).continuousAt.comp'
        (f := fun c : Real => (c, t)) (x := 1) hpair
  exact (hcont.tendsto).mono_left nhdsWithin_le_nhds

theorem tendsto_elementaryPoleIntegrand_c_to_one
    (F : CompactLogTest) {t : Real} (ht : t ≠ 0) :
    Tendsto (fun c : Real => elementaryPoleIntegrand F c t)
      (𝓝[>] (1 : Real))
      (𝓝 (elementaryPoleIntegrand F 1 t)) := by
  have hvertical : ContinuousAt (fun c : Real => verticalPoint c t) 1 := by
    unfold verticalPoint
    fun_prop
  have hzero : verticalPoint 1 t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [verticalPoint] at hre
  have hone : verticalPoint 1 t - 1 ≠ 0 := by
    intro h
    apply ht
    have him := congrArg Complex.im h
    simpa [verticalPoint] using him
  have hfirst : ContinuousAt (fun c : Real => 1 / verticalPoint c t) 1 := by
    exact continuousAt_const.div hvertical hzero
  have hsecond : ContinuousAt (fun c : Real =>
      1 / (verticalPoint c t - 1)) 1 := by
    exact continuousAt_const.div (hvertical.sub continuousAt_const) hone
  have hweight : ContinuousAt (fun c : Real =>
      symmetrizedLaplaceWeight F (verticalPoint c t)) 1 := by
    unfold symmetrizedLaplaceWeight
    apply ContinuousAt.add
    · simpa only [Function.comp_apply] using
        (continuous_centeredLaplaceWeight F).continuousAt.comp'
          (f := fun c : Real => verticalPoint c t) (x := 1) hvertical
    · have hreflect : ContinuousAt (fun c : Real =>
          1 - verticalPoint c t) 1 :=
        continuousAt_const.sub hvertical
      simpa only [Function.comp_apply] using
        (continuous_centeredLaplaceWeight F).continuousAt.comp'
          (f := fun c : Real => 1 - verticalPoint c t) (x := 1) hreflect
  simpa only [elementaryPoleIntegrand] using
    ((((hfirst.add hsecond).neg.mul hweight).mul continuousAt_const).tendsto).mono_left
      nhdsWithin_le_nhds

/- The full boundary value is intentionally a contract: the pointwise brick
only supplies the L-series on `Re(s) > 1`; a proof at `Re(s) = 1` needs an
independent boundary theorem. -/
structure FullPrimeBoundaryContract
    (F : CompactLogTest) (T : Real) where
  c : Nat → Real
  c_gt_one : ∀ k, 1 < c k
  c_tendsto_one : Tendsto c atTop (𝓝 1)
  integral_tendsto : Tendsto
    (fun k => ∫ t : Real in (-T)..T,
      arithmeticLSeriesIntegrand F (c k) t)
    atTop (𝓝 (∫ t : Real in (-T)..T,
      arithmeticLSeriesIntegrand F 1 t))

theorem arithmetic_interval_readback_of_boundary_contract
    (F : CompactLogTest) (T : Real)
    (hcontract : FullPrimeBoundaryContract F T) :
    Tendsto
      (fun k => ∫ t : Real in (-T)..T,
        arithmeticLSeriesIntegrand F (hcontract.c k) t)
      atTop (𝓝 (∫ t : Real in (-T)..T,
        arithmeticLSeriesIntegrand F 1 t)) :=
  hcontract.integral_tendsto

end
end C1XiArithmeticIntervalReadback
end Source
end ConnesWeilRH
