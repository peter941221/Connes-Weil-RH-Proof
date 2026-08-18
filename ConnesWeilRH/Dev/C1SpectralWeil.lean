import ConnesWeilRH.Dev.C1LogPositiveBridge
import ConnesWeilRH.Source.CC20ZetaCounting

/-!
# C1SpectralWeil - the independent spectral side of the Weil formula

This module defines the zero-spectral expression that Gate 2 must identify
with `C1SameOwnerWeil.psi`.  The spectral value is built independently from
the completed Riemann xi function, its analytic zero multiplicities, and the
same `CompactLogTest` Laplace transform used by the arithmetic owner.

No explicit-formula equality, positivity theorem, or RH statement is assumed
or asserted here.  In particular, `gate2ExplicitFormula` includes summability
as a mathematical obligation rather than relying on the default value of a
divergent `tsum`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralWeil

open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open Complex MeromorphicOn
open scoped BigOperators

/-- The analytic multiplicity of a source nontrivial zero in the completed
Riemann xi function. -/
noncomputable def xiMultiplicity (rho : sourceNontrivialZeroSet) : Nat :=
  analyticOrderNatAt completedRiemannXi rho.1

/-- Every source nontrivial zero occurs in xi with strictly positive analytic
multiplicity.  This prevents the spectral sum from silently becoming a sum
over distinct points with unit or zero weights. -/
theorem xiMultiplicity_pos (rho : sourceNontrivialZeroSet) :
    0 < xiMultiplicity rho := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have horder : analyticOrderAt completedRiemannXi rho.1 ≠ 0 :=
    (differentiable_completedRiemannXi.analyticAt rho.1).analyticOrderAt_ne_zero.mpr
      (completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2)
  have hzeroNat : analyticOrderNatAt completedRiemannXi rho.1 = 0 := by
    simpa only [xiMultiplicity] using hzero
  apply horder
  rw [← Nat.cast_analyticOrderNatAt
    (completedRiemannXi_analyticOrderAt_ne_top rho.1)]
  simp only [hzeroNat, Nat.cast_zero]

/-- The functional equation maps a source xi zero to another source xi zero.
The subtype keeps that transport explicit so later finite orbit sums cannot
silently replace a zero with an arbitrary complex point. -/
noncomputable def oneSubXiZero (rho : sourceNontrivialZeroSet) :
    sourceNontrivialZeroSet :=
  ⟨1 - rho.1,
    sourceNontrivialZero_of_completedRiemannXi_eq_zero (by
      rw [completedRiemannXi_one_sub]
      exact completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2)⟩

@[simp] theorem oneSubXiZero_coe (rho : sourceNontrivialZeroSet) :
    (oneSubXiZero rho : Complex) = 1 - rho.1 :=
  rfl

/-- The functional-equation involution preserves the analytic multiplicity of
every xi zero.  This is an order-of-vanishing statement, not merely equality
of the two function values. -/
theorem xiMultiplicity_oneSub (rho : sourceNontrivialZeroSet) :
    xiMultiplicity (oneSubXiZero rho) = xiMultiplicity rho := by
  have hderiv : deriv (fun s : Complex => (1 : Complex) - s) rho.1 ≠ 0 := by
    rw [deriv_const_sub_id]
    norm_num
  have hcomp :
      analyticOrderAt
          (completedRiemannXi ∘ fun s : Complex => (1 : Complex) - s) rho.1 =
        analyticOrderAt completedRiemannXi (1 - rho.1) :=
    analyticOrderAt_comp_of_deriv_ne_zero
      (f := completedRiemannXi) (g := fun s : Complex => (1 : Complex) - s)
      (z₀ := rho.1) (analyticAt_const.sub analyticAt_id) hderiv
  have hinvariance :
      analyticOrderAt completedRiemannXi (1 - rho.1) =
        analyticOrderAt completedRiemannXi rho.1 := by
    rw [← hcomp]
    apply analyticOrderAt_congr
    filter_upwards with s
    simpa [Function.comp_def] using completedRiemannXi_one_sub s
  change analyticOrderNatAt completedRiemannXi (1 - rho.1) =
    analyticOrderNatAt completedRiemannXi rho.1
  exact congrArg ENat.toNat hinvariance

/-- Every xi zero away from the critical line has a functional-equation
representative strictly to the right of that line, with the same analytic
multiplicity.  The returned subtype is either the original zero or its
`s |-> 1 - s` image, so later spectral arguments retain the zero owner. -/
theorem exists_rightOfCriticalXiZero_of_re_ne_half
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2) :
    exists sigma : sourceNontrivialZeroSet,
      (1 / 2 : Real) < sigma.1.re /\
      xiMultiplicity sigma = xiMultiplicity rho /\
      (sigma = rho \/ sigma = oneSubXiZero rho) := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · refine ⟨oneSubXiZero rho, ?_, xiMultiplicity_oneSub rho, Or.inr rfl⟩
    simp only [oneSubXiZero_coe, Complex.sub_re, Complex.one_re]
    linarith
  · exact ⟨rho, hright, rfl, Or.inl rfl⟩

/-- The zero coordinate centered at the critical line. -/
noncomputable def centeredXiCoordinate (rho : sourceNontrivialZeroSet) : Complex :=
  rho.1 - (1 / 2 : Complex)

/-- One multiplicity-weighted spectral term. -/
noncomputable def spectralTerm
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) : Complex :=
  (xiMultiplicity rho : Complex) *
    CompactLogTest.laplaceAt F (centeredXiCoordinate rho)

/-- The nonnegative scalar majorant of one spectral term. -/
noncomputable def spectralNormTerm
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) : Real :=
  (xiMultiplicity rho : Real) *
    norm (CompactLogTest.laplaceAt F (centeredXiCoordinate rho))

theorem spectralNormTerm_nonnegative
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    0 ≤ spectralNormTerm F rho := by
  exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-- The scalar majorant is exactly the norm of the complex spectral term. -/
theorem norm_spectralTerm
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    norm (spectralTerm F rho) = spectralNormTerm F rho := by
  simp [spectralTerm, spectralNormTerm]

/-- Exponential weighting translates the bilateral Laplace variable.  This is
the coordinate identity needed to move the critical strip `[0,1]` to the
centered strip `[-1/2,1/2]`. -/
theorem laplaceAt_exponentialWeight_eq
    (F : CompactLogTest) (a s : Complex) :
    CompactLogTest.laplaceAt
        (CC20YoshidaConvolution.CompactLogTest.exponentialWeight F a) s =
      CompactLogTest.laplaceAt F (s + a) := by
  unfold CompactLogTest.laplaceAt
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Every compact log test has one quadratic vertical-strip bound.  The proof
uses the genuine positive-variable coordinate bridge and the existing Mellin
integration-by-parts estimate; compactness supplies a slightly larger positive
support interval. -/
theorem exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖CompactLogTest.laplaceAt F
              ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  let a : Real := Real.exp (-C1SameOwnerWeil.supportRadius F - 1)
  let b : Real := Real.exp (C1SameOwnerWeil.supportRadius F + 1)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hsupport :
      Function.support (C1LogPositiveBridge.toPositiveRouteTest F) ⊆
        Set.Ioo a b := by
    intro x hx
    have hxRaw : x ∈ Function.support (C1LogPositiveBridge.positiveRouteRaw F) := by
      simpa only [C1LogPositiveBridge.toPositiveRouteTest_apply,
        C1LogPositiveBridge.positiveRouteRaw] using hx
    have hbounds := C1LogPositiveBridge.positiveRouteRaw_support_subset F hxRaw
    constructor
    · exact lt_of_lt_of_le
        (Real.exp_lt_exp.mpr (by simp)) hbounds.1
    · exact lt_of_le_of_lt hbounds.2
        (Real.exp_lt_exp.mpr (by simp))
  obtain ⟨C, hC, hdecay⟩ :=
    CC20YoshidaTail.exists_uniform_mellin_vertical_quadratic_decay
      (C1LogPositiveBridge.toPositiveRouteTest F) ha hb hsupport
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  simpa only [C1LogPositiveBridge.mellin_toPositiveRouteTest_eq_laplaceAt] using
    hdecay sigma hsigma t

/-- Every compact log test also has a fourth-order vertical-strip bound.  This
uses the same positive-variable coordinate bridge as the quadratic estimate. -/
theorem exists_uniform_compactLog_laplaceAt_vertical_quartic_decay
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
            ‖CompactLogTest.laplaceAt F
              ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  let a : Real := Real.exp (-C1SameOwnerWeil.supportRadius F - 1)
  let b : Real := Real.exp (C1SameOwnerWeil.supportRadius F + 1)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hsupport :
      Function.support (C1LogPositiveBridge.toPositiveRouteTest F) ⊆
        Set.Ioo a b := by
    intro x hx
    have hxRaw : x ∈ Function.support (C1LogPositiveBridge.positiveRouteRaw F) := by
      simpa only [C1LogPositiveBridge.toPositiveRouteTest_apply,
        C1LogPositiveBridge.positiveRouteRaw] using hx
    have hbounds := C1LogPositiveBridge.positiveRouteRaw_support_subset F hxRaw
    constructor
    · exact lt_of_lt_of_le
        (Real.exp_lt_exp.mpr (by simp)) hbounds.1
    · exact lt_of_le_of_lt hbounds.2
        (Real.exp_lt_exp.mpr (by simp))
  obtain ⟨C, hC, hdecay⟩ :=
    CC20YoshidaTail.exists_uniform_mellin_vertical_quartic_decay
      (C1LogPositiveBridge.toPositiveRouteTest F) ha hb hsupport
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  simpa only [C1LogPositiveBridge.mellin_toPositiveRouteTest_eq_laplaceAt] using
    hdecay sigma hsigma t

/-- Centered form of the uniform quadratic decay.  Its real coordinate is
`sigma - 1/2`, exactly matching `rho - 1/2` on the xi spectrum. -/
theorem exists_uniform_centered_laplaceAt_vertical_quadratic_decay
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖CompactLogTest.laplaceAt F
              (((sigma - 1 / 2 : Real) : Complex) +
                (t : Complex) * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay
      (CC20YoshidaConvolution.CompactLogTest.exponentialWeight F
        (-(1 / 2 : Real)))
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  have hbound := hdecay sigma hsigma t
  rw [laplaceAt_exponentialWeight_eq] at hbound
  have harg :
      ((sigma : Complex) + (t : Complex) * Complex.I) +
          (-(1 / 2 : Real) : Complex) =
        ((sigma - 1 / 2 : Real) : Complex) +
          (t : Complex) * Complex.I := by
    push_cast
    ring
  simpa only [harg] using hbound

/-- Centered fourth-order Laplace decay on the full source critical strip. -/
theorem exists_uniform_centered_laplaceAt_vertical_quartic_decay
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
            ‖CompactLogTest.laplaceAt F
              (((sigma - 1 / 2 : Real) : Complex) +
                (t : Complex) * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_compactLog_laplaceAt_vertical_quartic_decay
      (CC20YoshidaConvolution.CompactLogTest.exponentialWeight F
        (-(1 / 2 : Real)))
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  have hbound := hdecay sigma hsigma t
  rw [laplaceAt_exponentialWeight_eq] at hbound
  have harg :
      ((sigma : Complex) + (t : Complex) * Complex.I) +
          (-(1 / 2 : Real) : Complex) =
        ((sigma - 1 / 2 : Real) : Complex) +
          (t : Complex) * Complex.I := by
    push_cast
    ring
  simpa only [harg] using hbound

/-- The centered transform of every source nontrivial zero satisfies one
quadratic bound, uniformly and without assuming RH. -/
theorem exists_spectral_laplaceAt_quadratic_bound (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧ ∀ rho : sourceNontrivialZeroSet,
      ‖rho.1.im / (2 * Real.pi)‖ ^ 2 *
          ‖CompactLogTest.laplaceAt F (centeredXiCoordinate rho)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_centered_laplaceAt_vertical_quadratic_decay F
  refine ⟨C, hC, ?_⟩
  intro rho
  have hre : rho.1.re ∈ Set.Icc (0 : Real) 1 :=
    ⟨(sourceNontrivialZero_zero_lt_re rho.2).le,
      (sourceNontrivialZero_re_lt_one rho.2).le⟩
  have hbound := hdecay rho.1.re hre rho.1.im
  have harg : centeredXiCoordinate rho =
      (((rho.1.re - 1 / 2 : Real) : Complex) +
        (rho.1.im : Complex) * Complex.I) := by
    apply Complex.ext <;> simp [centeredXiCoordinate]
  simpa only [harg] using hbound

/-- Source zeros grouped by the least strict dyadic bound for the absolute
imaginary coordinate.  Unlike a distance shell around a selected zero, this
partition matches the symmetric-height multiplicity count directly. -/
noncomputable def spectralHeightShell (n : Nat) :
    Set sourceNontrivialZeroSet :=
  {rho | dyadicShellIndex |rho.1.im| = n}

theorem spectralHeightShell_partition :
    forall rho : sourceNontrivialZeroSet,
      ExistsUnique (fun n => rho ∈ spectralHeightShell n) := by
  intro rho
  refine ⟨dyadicShellIndex |rho.1.im|, rfl, ?_⟩
  intro n hn
  exact hn.symm

theorem spectralHeightShell_finite (n : Nat) :
    (spectralHeightShell n).Finite := by
  apply (sourceNontrivialZerosInSymmetricHeight_finite
    ((2 : Real) ^ (n + 1))).subset
  intro rho hrho
  change |rho.1.im| <= (2 : Real) ^ (n + 1)
  change dyadicShellIndex |rho.1.im| = n at hrho
  rw [← hrho]
  exact (lt_two_pow_succ_dyadicShellIndex |rho.1.im|).le

/-- Analytic multiplicity mass in one exact height shell. -/
noncomputable def spectralHeightMultiplicity (n : Nat) : Real :=
  ∑' rho : spectralHeightShell n, (xiMultiplicity rho : Real)

theorem spectralHeightMultiplicity_nonnegative (n : Nat) :
    0 <= spectralHeightMultiplicity n := by
  exact tsum_nonneg fun rho => Nat.cast_nonneg (xiMultiplicity rho)

/-- A finite zeroth shell plus geometrically controlled weighted tail shells
are summable when the pointwise tail decays quadratically.  The weight is kept
abstract so the theorem counts analytic multiplicity rather than merely
distinct spectral points. -/
theorem summable_of_shifted_geometric_shell_weight_bound
    {alpha : Type*} (f weight : alpha -> Real) (shell : Nat -> Set alpha)
    (hf : forall x, 0 <= f x)
    (hpartition : forall x, ExistsUnique (fun n => x ∈ shell n))
    (hfinite : forall n, (shell n).Finite)
    {K B q : Real} (hB : 0 <= B) (hq : 0 <= q) (hq4 : q < 4)
    (hmass : forall n,
      (∑' x : shell (n + 1), weight x) <= K * q ^ n)
    (hpoint : forall n (x : shell (n + 1)),
      f x <= weight x * (B / ((2 : Real) ^ n) ^ 2)) :
    Summable f := by
  rw [summable_partition hf hpartition]
  constructor
  · intro n
    letI := (hfinite n).fintype
    exact (hasSum_fintype (fun x : shell n => f x)).summable
  · rw [← summable_nat_add_iff
      (f := fun n => ∑' x : shell n, f x) 1]
    have hratioNonneg : 0 <= q / 4 := div_nonneg hq (by norm_num)
    have hratioLt : q / 4 < 1 :=
      (div_lt_one (by norm_num : (0 : Real) < 4)).mpr hq4
    have hgeometric : Summable (fun n : Nat => (q / 4) ^ n) :=
      summable_geometric_of_lt_one hratioNonneg hratioLt
    refine Summable.of_nonneg_of_le
      (fun n => tsum_nonneg fun x => hf x) ?_
      (hgeometric.mul_left (K * B))
    intro n
    letI := (hfinite (n + 1)).fintype
    have hmassN := hmass n
    rw [tsum_fintype] at hmassN
    rw [tsum_fintype]
    calc
      (∑ x : shell (n + 1), f x) <=
          ∑ x : shell (n + 1),
            weight x * (B / ((2 : Real) ^ n) ^ 2) := by
              exact Finset.sum_le_sum fun x _hx => hpoint n x
      _ = (∑ x : shell (n + 1), weight x) *
          (B / ((2 : Real) ^ n) ^ 2) := by
            rw [Finset.sum_mul]
      _ <= (K * q ^ n) * (B / ((2 : Real) ^ n) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hmassN
              (div_nonneg hB (sq_nonneg _))
      _ = K * B * (q / 4) ^ n := by
            rw [div_pow]
            norm_num [pow_two, mul_pow]
            have hfour :
                (2 : Real) ^ n * (2 : Real) ^ n = 4 ^ n := by
              rw [← mul_pow]
              norm_num
            rw [hfour]
            ring

/-- The existing uniform vertical estimate gives the exact quadratic dyadic
tail bound needed by the multiplicity-aware shell consumer.  Shell zero is
left finite, so this statement makes no assumption that xi has no real zero. -/
theorem exists_spectral_laplaceAt_dyadic_tail_bound (F : CompactLogTest) :
    ∃ B : Real, 0 <= B ∧
      forall n (rho : spectralHeightShell (n + 1)),
        norm (CompactLogTest.laplaceAt F (centeredXiCoordinate rho)) <=
          B / ((2 : Real) ^ n) ^ 2 := by
  obtain ⟨C, hC, hdecay⟩ := exists_spectral_laplaceAt_quadratic_bound F
  refine ⟨(2 * Real.pi) ^ 2 * C, mul_nonneg (sq_nonneg _) hC, ?_⟩
  intro n rho
  have hheightLarge : (2 : Real) ^ (n + 1) <= |rho.1.1.im| :=
    pow_succ_le_of_dyadicShellIndex_eq_succ rho.2
  have hheight : (2 : Real) ^ n <= |rho.1.1.im| := by
    calc
      (2 : Real) ^ n <= (2 : Real) ^ (n + 1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : Real) <= 2) n]
      _ <= |rho.1.1.im| := hheightLarge
  have hdenom : 0 < 2 * Real.pi := by positivity
  have hscaled :
      (2 : Real) ^ n / (2 * Real.pi) <=
        |rho.1.1.im| / (2 * Real.pi) :=
    div_le_div_of_nonneg_right hheight hdenom.le
  have hscaledNonneg : 0 <= (2 : Real) ^ n / (2 * Real.pi) := by
    positivity
  have hscaledSq :
      ((2 : Real) ^ n / (2 * Real.pi)) ^ 2 <=
        (|rho.1.1.im| / (2 * Real.pi)) ^ 2 :=
    pow_le_pow_left₀ hscaledNonneg hscaled 2
  have hdecayRho := hdecay rho
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hdenom.le] at hdecayRho
  have hsmallDecay :
      ((2 : Real) ^ n / (2 * Real.pi)) ^ 2 *
          norm (CompactLogTest.laplaceAt F (centeredXiCoordinate rho)) <= C :=
    (mul_le_mul_of_nonneg_right hscaledSq (norm_nonneg _)).trans hdecayRho
  have hsmallDecay' :
      (((2 : Real) ^ n) ^ 2 *
          norm (CompactLogTest.laplaceAt F (centeredXiCoordinate rho))) /
            (2 * Real.pi) ^ 2 <= C := by
    convert hsmallDecay using 1
    field_simp [Real.pi_ne_zero]
  have hproduct := (div_le_iff₀ (sq_pos_of_pos hdenom)).mp hsmallDecay'
  rw [le_div_iff₀ (sq_pos_of_pos (pow_pos (by norm_num) n))]
  nlinarith

/-- Geometric growth below the quadratic threshold for the analytic
multiplicity mass is sufficient for absolute convergence of the independent
spectral side. -/
theorem spectralSummable_of_geometric_heightMultiplicity_bound
    (F : CompactLogTest) {K q : Real} (hq : 0 <= q) (hq4 : q < 4)
    (hmass : forall n,
      spectralHeightMultiplicity (n + 1) <= K * q ^ n) :
    Summable (spectralTerm F) := by
  obtain ⟨B, hB, hpoint⟩ :=
    exists_spectral_laplaceAt_dyadic_tail_bound F
  apply Summable.of_norm
  simpa only [norm_spectralTerm] using
    (summable_of_shifted_geometric_shell_weight_bound
      (spectralNormTerm F) (fun rho => (xiMultiplicity rho : Real))
      spectralHeightShell (spectralNormTerm_nonnegative F)
      spectralHeightShell_partition spectralHeightShell_finite hB hq hq4
      (by simpa only [spectralHeightMultiplicity] using hmass)
      (by
        intro n rho
        unfold spectralNormTerm
        exact mul_le_mul_of_nonneg_left (hpoint n rho)
          (Nat.cast_nonneg (xiMultiplicity rho))))

/-- The finite set of source zeros with imaginary part in `[-T, T]`. -/
noncomputable def finiteHeightZeros (T : Real) :
    Finset sourceNontrivialZeroSet :=
  (sourceNontrivialZerosInSymmetricHeight_finite T).toFinset

@[simp] theorem mem_finiteHeightZeros_iff
    (T : Real) (rho : sourceNontrivialZeroSet) :
    rho ∈ finiteHeightZeros T ↔ |rho.1.im| ≤ T := by
  simp [finiteHeightZeros, sourceNontrivialZerosInSymmetricHeight]

/-- The total analytic multiplicity in the symmetric height window. -/
noncomputable def finiteHeightMultiplicity (T : Real) : Nat :=
  ∑ rho ∈ finiteHeightZeros T, xiMultiplicity rho

/-- Inside a closed ball, the xi divisor reads back the analytic multiplicity
attached to a source nontrivial zero. -/
theorem xiMultiplicity_cast_eq_divisor_of_mem_closedBall
    (rho : sourceNontrivialZeroSet) {c : Complex} {r : Real}
    (hrho : rho.1 ∈ Metric.closedBall c |r|) :
    (xiMultiplicity rho : Int) =
      divisor completedRiemannXi (Metric.closedBall c |r|) rho.1 := by
  rw [(analyticOnNhd_completedRiemannXi _).divisor_apply hrho]
  rw [← Nat.cast_analyticOrderNatAt
    (completedRiemannXi_analyticOrderAt_ne_top rho.1)]
  simp [xiMultiplicity]

/-- The multiplicity mass in `[-T,T]` is bounded by the xi divisor mass in
the radius `|T+2|` ball centered at the nonzero Jensen base point `2`. -/
theorem finiteHeightMultiplicity_le_xi_divisor_mass (T : Real) :
    (finiteHeightMultiplicity T : Int) ≤
      ∑ᶠ z : Complex,
        divisor completedRiemannXi (Metric.closedBall 2 |T + 2|) z := by
  classical
  let zeros := finiteHeightZeros T
  let d := divisor completedRiemannXi (Metric.closedBall 2 |T + 2|)
  have hsupport : (Function.support d).Finite :=
    d.finiteSupport (isCompact_closedBall 2 |T + 2|)
  have hzeroBall (rho : sourceNontrivialZeroSet) (hrho : rho ∈ zeros) :
      rho.1 ∈ Metric.closedBall 2 |T + 2| := by
    have hheight : rho ∈ sourceNontrivialZerosInSymmetricHeight T := by
      simpa [zeros, finiteHeightZeros] using hrho
    have hbase : rho.1 ∈ sourceNontrivialZerosInClosedBall 2 (T + 2) :=
      sourceNontrivialZerosInSymmetricHeight_map_subset_closedBall_two
        ⟨rho, hheight, rfl⟩
    exact Metric.closedBall_subset_closedBall (le_abs_self (T + 2)) hbase.1
  have himageSubset :
      Finset.image (fun rho : sourceNontrivialZeroSet => rho.1) zeros ⊆
        hsupport.toFinset := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, rfl⟩
    rw [hsupport.mem_toFinset, Function.mem_support]
    rw [← xiMultiplicity_cast_eq_divisor_of_mem_closedBall rho (hzeroBall rho hrho)]
    exact_mod_cast (Nat.ne_of_gt (xiMultiplicity_pos rho))
  calc
    (finiteHeightMultiplicity T : Int) =
        ∑ rho ∈ zeros, (xiMultiplicity rho : Int) := by
          simp [finiteHeightMultiplicity, zeros]
    _ = ∑ z ∈ Finset.image
          (fun rho : sourceNontrivialZeroSet => rho.1) zeros, d z := by
      rw [Finset.sum_image Subtype.val_injective.injOn]
      apply Finset.sum_congr rfl
      intro rho hrho
      exact xiMultiplicity_cast_eq_divisor_of_mem_closedBall rho
        (hzeroBall rho hrho)
    _ ≤ ∑ z ∈ hsupport.toFinset, d z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himageSubset
      intro z _hz _hnotImage
      exact (analyticOnNhd_completedRiemannXi _).divisor_nonneg z
    _ = ∑ᶠ z : Complex, d z := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro z hz
      exact hsupport.mem_toFinset.mpr hz

/-- Real-cast form of the preceding divisor-mass comparison. -/
theorem finiteHeightMultiplicity_cast_le_xi_divisor_mass (T : Real) :
    (finiteHeightMultiplicity T : Real) ≤
      ((∑ᶠ z : Complex,
        divisor completedRiemannXi (Metric.closedBall 2 |T + 2|) z : Int) : Real) := by
  exact_mod_cast finiteHeightMultiplicity_le_xi_divisor_mass T

/-- Jensen's inequality with analytic multiplicities, rather than merely the
number of distinct source zeros. -/
theorem finiteHeightMultiplicity_cast_le_of_xi_sphere_bound
    {T R M : Real} (hT : -2 < T) (hR : T + 2 < |R|)
    (hM : 1 ≤ M)
    (hsphere : ∀ z ∈ Metric.sphere (2 : Complex) |R|,
      ‖completedRiemannXi z‖ ≤ M) :
    (finiteHeightMultiplicity T : Real) ≤
      Real.log (M / ‖completedRiemannXi 2‖) /
        Real.log (R / (T + 2)) := by
  have hTtwo : 0 < T + 2 := by linarith
  calc
    (finiteHeightMultiplicity T : Real) ≤
        ((∑ᶠ z : Complex,
          divisor completedRiemannXi (Metric.closedBall 2 |T + 2|) z : Int) : Real) :=
      finiteHeightMultiplicity_cast_le_xi_divisor_mass T
    _ ≤ Real.log (M / ‖completedRiemannXi 2‖) /
        Real.log (R / (T + 2)) :=
      (analyticOnNhd_completedRiemannXi _).sum_divisor_le
        (by simpa [abs_of_pos hTtwo] using hTtwo)
        (by simpa [abs_of_pos hTtwo] using hR)
        hM completedRiemannXi_two_ne_zero hsphere

/-- Exponential xi growth on the doubled Jensen circle controls the total
analytic multiplicity in a symmetric-height window. -/
theorem finiteHeightMultiplicity_cast_le_of_xi_exp_sphere_bound
    {T G : Real} (hT : -2 < T) (hG : 0 ≤ G)
    (hsphere : ∀ z ∈ Metric.sphere (2 : Complex) (2 * (T + 2)),
      ‖completedRiemannXi z‖ ≤ Real.exp G) :
    (finiteHeightMultiplicity T : Real) ≤
      (G - Real.log ‖completedRiemannXi 2‖) / Real.log 2 := by
  have hTtwo : 0 < T + 2 := by linarith
  have hRadius : 0 < 2 * (T + 2) := mul_pos (by norm_num) hTtwo
  have hJensen := finiteHeightMultiplicity_cast_le_of_xi_sphere_bound
    (T := T) (R := 2 * (T + 2)) (M := Real.exp G) hT
    (by rw [abs_of_pos hRadius]; linarith)
    (by simpa using Real.one_le_exp hG)
    (by simpa [abs_of_pos hRadius] using hsphere)
  have hxiNorm : ‖completedRiemannXi 2‖ ≠ 0 :=
    norm_ne_zero_iff.mpr completedRiemannXi_two_ne_zero
  calc
    (finiteHeightMultiplicity T : Real) ≤
        Real.log (Real.exp G / ‖completedRiemannXi 2‖) /
          Real.log (2 * (T + 2) / (T + 2)) := hJensen
    _ = (G - Real.log ‖completedRiemannXi 2‖) / Real.log 2 := by
      rw [Real.log_div (Real.exp_ne_zero G) hxiNorm, Real.log_exp]
      congr 2
      field_simp

/-- The symmetric-height spectral partial sum, with analytic multiplicities. -/
noncomputable def finiteSpectralSum
    (F : CompactLogTest) (T : Real) : Complex :=
  ∑ rho ∈ finiteHeightZeros T, spectralTerm F rho

/-- Absolute summability of the multiplicity-weighted zero spectrum. -/
def SpectralSummable (F : CompactLogTest) : Prop :=
  Summable (spectralTerm F)

/-- The real spectral value in the centered xi coordinate.  Consumers must
carry `SpectralSummable F`; the definition alone does not claim convergence. -/
noncomputable def spectralWeilValue (F : CompactLogTest) : Real :=
  (tsum (spectralTerm F)).re

/-- Gate 2a: the unconditional Riemann-Weil explicit formula on one
`CompactLogTest` owner.  Both sides are independently defined. -/
def gate2ExplicitFormula (F : CompactLogTest) : Prop :=
  SpectralSummable F ∧
    C1SameOwnerWeil.psi F = spectralWeilValue F

/-- The square-specialized Gate 2 statement keeps the same route test through
the arithmetic convolution square and the spectral expression. -/
def gate2ExplicitFormulaOnSquare (g : CompactLogTest) : Prop :=
  gate2ExplicitFormula g.convolutionSquare

/-- Every zero in the exact shell `n+1` (absolute imaginary part lying in
`[(2)^(n+1), (2)^(n+2))`) lies in the symmetric-height window of radius
`(2)^(n+2)`.  This containment lets shell multiplicity mass be charged against
the height-window multiplicity mass. -/
theorem spectralHeightShell_subset_symmetricHeight (n : Nat) :
    spectralHeightShell (n + 1) ⊆
      sourceNontrivialZerosInSymmetricHeight ((2 : Real) ^ (n + 2)) := by
  intro rho hrho
  change dyadicShellIndex |rho.1.im| = n + 1 at hrho
  change |rho.1.im| <= (2 : Real) ^ (n + 2)
  have hlt := lt_two_pow_succ_dyadicShellIndex |rho.1.im|
  rw [hrho] at hlt
  simpa only [Nat.add_assoc] using hlt.le

/-- A finite subtype sum is the corresponding sum over the finite set.  The
subtype equivalence is explicit so the analytic multiplicity mass cannot lose
or duplicate an indexed zero when it is read back as a `Finset` sum. -/
theorem tsum_finite_subtype_eq_sum_toFinset {α : Type*} {s : Set α}
    (hs : s.Finite) (f : α → ℝ) :
    (∑' x : {x // x ∈ s}, f x) =
      ∑ x ∈ hs.toFinset, f x := by
  letI : Fintype s := hs.fintype
  rw [tsum_fintype]
  symm
  apply Finset.sum_subtype
  intro x
  exact hs.mem_toFinset

/-- The analytic multiplicity mass in one dyadic shell is bounded by the
corresponding symmetric-height window.  This preserves multiplicities; the
older cardinality count cannot supply this bound. -/
theorem spectralHeightMultiplicity_le_finiteHeightMultiplicity (n : Nat) :
    spectralHeightMultiplicity (n + 1) ≤
      (finiteHeightMultiplicity ((2 : Real) ^ (n + 2)) : Real) := by
  classical
  let shell := spectralHeightShell (n + 1)
  let T : Real := (2 : Real) ^ (n + 2)
  have hfinite : shell.Finite := by
    simpa only [shell] using spectralHeightShell_finite (n + 1)
  have hsubset : hfinite.toFinset ⊆ finiteHeightZeros T := by
    intro rho hrho
    rw [mem_finiteHeightZeros_iff]
    apply spectralHeightShell_subset_symmetricHeight n
    exact hfinite.mem_toFinset.mp hrho
  calc
    spectralHeightMultiplicity (n + 1) =
        ∑ rho ∈ hfinite.toFinset, (xiMultiplicity rho : Real) := by
          unfold spectralHeightMultiplicity
          exact tsum_finite_subtype_eq_sum_toFinset hfinite
            (fun rho => (xiMultiplicity rho : Real))
    _ ≤ ∑ rho ∈ finiteHeightZeros T, (xiMultiplicity rho : Real) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro rho _ _
          exact Nat.cast_nonneg (xiMultiplicity rho)
    _ = (finiteHeightMultiplicity T : Real) := by
          simp only [finiteHeightMultiplicity, Nat.cast_sum]

end C1SpectralWeil
end Source
end ConnesWeilRH
