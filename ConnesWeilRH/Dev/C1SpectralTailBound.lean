import ConnesWeilRH.Dev.C1SpectralSummability
import ConnesWeilRH.Dev.C1XiGlobalZeroSum

/-!
# C1SpectralTailBound - quantitative spectral tails from a fourth-order test bound

The Yoshida construction supplies a distance-weighted fourth-order estimate
for its selected convolution square.  This module converts that local test
estimate into a multiplicity-aware bound on every high spectral shell.  It
does not claim a negative global spectral sum; finite-prefix control remains
a separate consumer.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralTailBound

open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralSummability
open C1SpectralWeil
open C1XiGlobalZeroSum
open scoped BigOperators

/-- A compact-log test has a fourth-order tail around `rho` when both
functional-equation distances multiply the centered transform.  The condition
is stated on the whole critical strip so it can be specialized to the exact
source xi-zero index without changing test-space owners. -/
def FourthOrderSpectralTail
    (F : CompactLogTest) (rho : Complex) (T epsilon : Real) : Prop :=
  forall z : Complex, z.re ∈ Set.Icc (0 : Real) 1 ->
    T ≤ |z.im| -> 1 ≤ |z.im| -> 2 * |rho.im| ≤ |z.im| ->
      ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
          ‖CompactLogTest.laplaceAt F (z - 1 / 2)‖ < epsilon ^ 2

/-- A fourth-order selected-owner tail gives a multiplicity-weighted
quadratic dyadic bound on every sufficiently high source-zero shell.  The
quadratic form is deliberately weaker than the available fourth-order decay:
it is the exact shape consumed by the existing geometric shell summation API.
-/
theorem spectralTerm_norm_tail_instance_of_fourthOrderTail
    (F : CompactLogTest) (rho : Complex) (T epsilon : Real)
    (htail : FourthOrderSpectralTail F rho T epsilon)
    (n n0 : Nat) (hn : n0 ≤ n)
    (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.im| ≤ (2 : Real) ^ (n0 + 1))
    (sigma : spectralHeightShell (n + 1)) :
    ‖spectralTerm F sigma.1‖ ≤
      (xiMultiplicity sigma.1 : Real) *
        (epsilon ^ 2 / ((2 : Real) ^ n) ^ 2) := by
  have hshell : (2 : Real) ^ (n + 1) ≤ |sigma.1.1.im| :=
    shell_lower_im sigma.2
  have hpow : (2 : Real) ^ (n0 + 1) ≤ (2 : Real) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hheight : (2 : Real) ^ (n0 + 1) ≤ |sigma.1.1.im| :=
    hpow.trans hshell
  have hstrip : sigma.1.1.re ∈ Set.Icc (0 : Real) 1 :=
    ⟨(sourceNontrivialZero_zero_lt_re sigma.1.2).le,
      (sourceNontrivialZero_re_lt_one sigma.1.2).le⟩
  have hone : 1 ≤ |sigma.1.1.im| := by
    calc
      (1 : Real) ≤ (2 : Real) ^ (n0 + 1) := one_le_pow₀ (by norm_num)
      _ ≤ |sigma.1.1.im| := hheight
  have htailSigma := htail sigma.1.1 hstrip (hT.trans hheight) hone
    (hrhoHeight.trans hheight)
  have hdistAbs :
      |sigma.1.1.im| - |rho.im| ≤ |sigma.1.1.im - rho.im| :=
    abs_sub_abs_le_abs_sub sigma.1.1.im rho.im
  have hdistanceIm : (2 : Real) ^ n ≤ |sigma.1.1.im - rho.im| := by
    have hshell' := hshell
    rw [pow_succ] at hshell'
    nlinarith [hshell', hrhoHeight.trans hheight, hdistAbs,
      pow_nonneg (by norm_num : (0 : Real) ≤ 2) n]
  have hdistanceLeft : (2 : Real) ^ n ≤ ‖sigma.1.1 - rho‖ := by
    calc
      (2 : Real) ^ n ≤ |sigma.1.1.im - rho.im| := hdistanceIm
      _ = |(sigma.1.1 - rho).im| := by simp
      _ ≤ ‖sigma.1.1 - rho‖ := Complex.abs_im_le_norm _
  have hdistanceRight : (2 : Real) ^ n ≤ ‖(1 - star sigma.1.1) - rho‖ := by
    calc
      (2 : Real) ^ n ≤ |sigma.1.1.im - rho.im| := hdistanceIm
      _ = |((1 - star sigma.1.1) - rho).im| := by simp
      _ ≤ ‖(1 - star sigma.1.1) - rho‖ := Complex.abs_im_le_norm _
  have hpowNonneg : 0 ≤ (2 : Real) ^ n :=
    pow_nonneg (by norm_num) _
  have hdistanceLeftSq : ((2 : Real) ^ n) ^ 2 ≤ ‖sigma.1.1 - rho‖ ^ 2 :=
    pow_le_pow_left₀ hpowNonneg hdistanceLeft 2
  have hdistanceRightSq : ((2 : Real) ^ n) ^ 2 ≤
      ‖(1 - star sigma.1.1) - rho‖ ^ 2 :=
    pow_le_pow_left₀ hpowNonneg hdistanceRight 2
  have hproduct :
      ((2 : Real) ^ n) ^ 2 * ((2 : Real) ^ n) ^ 2 ≤
        ‖sigma.1.1 - rho‖ ^ 2 * ‖(1 - star sigma.1.1) - rho‖ ^ 2 :=
    mul_le_mul hdistanceLeftSq hdistanceRightSq (sq_nonneg _) (sq_nonneg _)
  have hscaled :
      (((2 : Real) ^ n) ^ 2 * ((2 : Real) ^ n) ^ 2) *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ ≤
        ‖sigma.1.1 - rho‖ ^ 2 * ‖(1 - star sigma.1.1) - rho‖ ^ 2 *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ :=
    mul_le_mul_of_nonneg_right hproduct (norm_nonneg _)
  have hfourth :
      (((2 : Real) ^ n) ^ 2 * ((2 : Real) ^ n) ^ 2) *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ ≤ epsilon ^ 2 :=
    (hscaled.trans_lt htailSigma).le
  have hpowSqOne : 1 ≤ ((2 : Real) ^ n) ^ 2 := by
    have hpowOne : 1 ≤ (2 : Real) ^ n := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg ((2 : Real) ^ n - 1)]
  have hquadraticLower :
      ((2 : Real) ^ n) ^ 2 *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ ≤
        (((2 : Real) ^ n) ^ 2 * ((2 : Real) ^ n) ^ 2) *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ := by
    calc
      ((2 : Real) ^ n) ^ 2 *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ =
        1 * (((2 : Real) ^ n) ^ 2 *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖) := by ring
      _ ≤ ((2 : Real) ^ n) ^ 2 *
          (((2 : Real) ^ n) ^ 2 *
            ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖) := by
          exact mul_le_mul_of_nonneg_right hpowSqOne
            (mul_nonneg (sq_nonneg _) (norm_nonneg _))
      _ = (((2 : Real) ^ n) ^ 2 * ((2 : Real) ^ n) ^ 2) *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ := by ring
  have hquadratic :
      ((2 : Real) ^ n) ^ 2 *
          ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ ≤ epsilon ^ 2 :=
    hquadraticLower.trans hfourth
  have hdenomPos : 0 < ((2 : Real) ^ n) ^ 2 :=
    sq_pos_of_pos (pow_pos (by norm_num) _)
  have hlaplace :
      ‖CompactLogTest.laplaceAt F (sigma.1.1 - 1 / 2)‖ ≤
        epsilon ^ 2 / ((2 : Real) ^ n) ^ 2 := by
    apply (le_div_iff₀ hdenomPos).mpr
    simpa [mul_comm] using hquadratic
  rw [norm_spectralTerm]
  unfold spectralNormTerm
  exact mul_le_mul_of_nonneg_left hlaplace
    (Nat.cast_nonneg (xiMultiplicity sigma.1))

/-- The complete high-shell norm tail is bounded by a geometric series.  The
factor `3 / 4` is the conservative combination of the proved multiplicity
mass growth `3^n` with the quadratic weakening of the available fourth-order
decay.  Because the construction may choose `epsilon` arbitrarily, this is
already an arbitrarily small multiplicity-weighted spectral tail bound. -/
theorem spectralTail_norm_shellSum_le_of_fourthOrderTail
    (F : CompactLogTest) (rho : Complex) (T epsilon : Real)
    (htail : FourthOrderSpectralTail F rho T epsilon)
    (n0 : Nat)
    (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.im| ≤ (2 : Real) ^ (n0 + 1)) :
    (∑' m : Nat, ∑' sigma : spectralHeightShell (m + n0 + 1),
      ‖spectralTerm F sigma.1‖) ≤
      4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 := by
  have hnormSum : Summable (fun sigma : sourceNontrivialZeroSet =>
      ‖spectralTerm F sigma‖) := by
    exact summable_of_shell_weight_tail_bound
      (f := fun sigma => ‖spectralTerm F sigma‖)
      (weight := fun sigma => (xiMultiplicity sigma : Real))
      (shell := spectralHeightShell)
      (hf := fun sigma => norm_nonneg _)
      (hpartition := spectralHeightShell_partition)
      (hfinite := spectralHeightShell_finite)
      (K := spectralMultiplicityConstant) (B := epsilon ^ 2) (q := 3)
      (n0 := n0)
      (hB := sq_nonneg epsilon)
      (hq := by norm_num) (hq4 := by norm_num)
      (hmass := fun n => by
        simpa [spectralHeightMultiplicity] using
          spectralHeightMultiplicity_geometric_bound n)
      (hpoint := fun n hn sigma =>
        spectralTerm_norm_tail_instance_of_fourthOrderTail
          F rho T epsilon htail n n0 hn hT hrhoHeight sigma)
  have hpartitionSum :
      (∀ n : Nat, Summable (fun sigma : spectralHeightShell n =>
          ‖spectralTerm F sigma.1‖)) ∧
        Summable (fun n : Nat => ∑' sigma : spectralHeightShell n,
          ‖spectralTerm F sigma.1‖) :=
    (summable_partition (fun sigma : sourceNontrivialZeroSet =>
      norm_nonneg _) spectralHeightShell_partition).mp hnormSum
  have htailSum : Summable (fun m : Nat =>
      ∑' sigma : spectralHeightShell (m + n0 + 1),
        ‖spectralTerm F sigma.1‖) := by
    refine (summable_nat_add_iff
      (f := fun k : Nat => ∑' sigma : spectralHeightShell k,
        ‖spectralTerm F sigma.1‖) (n0 + 1)).mpr hpartitionSum.2
  have hperM (m : Nat) :
      (∑' sigma : spectralHeightShell (m + n0 + 1),
        ‖spectralTerm F sigma.1‖) ≤
        spectralMultiplicityConstant * epsilon ^ 2 *
          (3 / 4 : Real) ^ (m + n0) := by
    letI := (spectralHeightShell_finite (m + n0 + 1)).fintype
    have hmassN' :
        (∑' sigma : spectralHeightShell (m + n0 + 1),
          (xiMultiplicity sigma.1 : Real)) ≤
          spectralMultiplicityConstant * 3 ^ (m + n0) := by
      simpa [spectralHeightMultiplicity] using
        spectralHeightMultiplicity_geometric_bound (m + n0)
    have hmassN :
        (∑ sigma : spectralHeightShell (m + n0 + 1),
          (xiMultiplicity sigma.1 : Real)) ≤
          spectralMultiplicityConstant * 3 ^ (m + n0) := by
      rw [tsum_fintype] at hmassN'
      exact hmassN'
    rw [tsum_fintype]
    calc
      (∑ sigma : spectralHeightShell (m + n0 + 1),
          ‖spectralTerm F sigma.1‖) ≤
          ∑ sigma : spectralHeightShell (m + n0 + 1),
            (xiMultiplicity sigma.1 : Real) *
              (epsilon ^ 2 / ((2 : Real) ^ (m + n0)) ^ 2) := by
              exact Finset.sum_le_sum fun sigma _hsigma =>
                spectralTerm_norm_tail_instance_of_fourthOrderTail
                  F rho T epsilon htail (m + n0) n0 (by omega)
                  hT hrhoHeight sigma
      _ = (∑ sigma : spectralHeightShell (m + n0 + 1),
            (xiMultiplicity sigma.1 : Real)) *
          (epsilon ^ 2 / ((2 : Real) ^ (m + n0)) ^ 2) := by
            rw [Finset.sum_mul]
      _ ≤ spectralMultiplicityConstant * 3 ^ (m + n0) *
          (epsilon ^ 2 / ((2 : Real) ^ (m + n0)) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hmassN
              (div_nonneg (sq_nonneg epsilon) (sq_nonneg _))
      _ = spectralMultiplicityConstant * epsilon ^ 2 *
          (3 / 4 : Real) ^ (m + n0) := by
            have hfour :
                ((2 : Real) ^ (m + n0)) ^ 2 =
                  4 ^ (m + n0) := by
              rw [pow_two, ← mul_pow]
              norm_num
            rw [hfour]
            calc
              _ = spectralMultiplicityConstant * epsilon ^ 2 *
                  ((3 : Real) ^ (m + n0) / 4 ^ (m + n0)) := by ring
              _ = _ := by rw [← div_pow]
  have hgeoConst : Summable (fun m : Nat =>
      spectralMultiplicityConstant * epsilon ^ 2 *
        (3 / 4 : Real) ^ (m + n0)) := by
    have hgeo : Summable (fun m : Nat => (3 / 4 : Real) ^ m) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (hgeo.mul_left (spectralMultiplicityConstant * epsilon ^ 2 *
      (3 / 4 : Real) ^ n0)).congr ?_
    intro m
    rw [pow_add]
    ring
  calc
    (∑' m : Nat, ∑' sigma : spectralHeightShell (m + n0 + 1),
        ‖spectralTerm F sigma.1‖) ≤
        ∑' m : Nat,
          spectralMultiplicityConstant * epsilon ^ 2 *
            (3 / 4 : Real) ^ (m + n0) := by
              exact htailSum.tsum_le_tsum (fun m => hperM m) hgeoConst
    _ = ∑' m : Nat,
          (spectralMultiplicityConstant * epsilon ^ 2 *
            (3 / 4 : Real) ^ n0) * (3 / 4 : Real) ^ m := by
          refine tsum_congr (fun m => ?_)
          rw [pow_add]
          ring
    _ = spectralMultiplicityConstant * epsilon ^ 2 *
        (3 / 4 : Real) ^ n0 * ∑' m : Nat, (3 / 4 : Real) ^ m := by
          rw [tsum_mul_left]
    _ = 4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
          ring_nf

/-- Every finite tail threshold has a dyadic shell start that dominates both
the construction threshold and the two-distance separation threshold. -/
theorem exists_dyadic_tail_start (T : Real) (rho : Complex) :
    ∃ n0 : Nat,
      T ≤ (2 : Real) ^ (n0 + 1) ∧
      2 * |rho.im| ≤ (2 : Real) ^ (n0 + 1) := by
  obtain ⟨n0, hn0⟩ := exists_lt_two_pow_succ (max T (2 * |rho.im|))
  refine ⟨n0, ?_, ?_⟩
  · exact (le_max_left _ _).trans hn0.le
  · exact (le_max_right _ _).trans hn0.le

/-- A dyadic tail start can always be moved far enough out that the geometric
tail budget is strictly below the positive analytic multiplicity of a chosen
source zero. -/
theorem exists_dyadic_tail_start_with_budget_lt_xiMultiplicity
    (T epsilon : Real) (rho : sourceNontrivialZeroSet) :
    ∃ n0 : Nat,
      T ≤ (2 : Real) ^ (n0 + 1) ∧
      2 * |rho.1.im| ≤ (2 : Real) ^ (n0 + 1) ∧
      4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 < (xiMultiplicity rho : Real) := by
  obtain ⟨nStart, hTStart, hrhoStart⟩ := exists_dyadic_tail_start T rho.1
  let A : Real := 4 * epsilon ^ 2 * spectralMultiplicityConstant
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg (by norm_num : (0 : Real) ≤ 4) (sq_nonneg epsilon))
      spectralMultiplicityConstant_nonneg
  have hxi : 0 < (xiMultiplicity rho : Real) := by
    exact_mod_cast xiMultiplicity_pos rho
  have hAplus : 0 < A + 1 := by linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
    (div_pos hxi hAplus) (by norm_num : (3 / 4 : Real) < 1)
  let n0 : Nat := max nStart m
  refine ⟨n0, ?_, ?_, ?_⟩
  · apply hTStart.trans
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · apply hrhoStart.trans
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · have hqNonneg : 0 ≤ (3 / 4 : Real) := by norm_num
    have hqLeOne : (3 / 4 : Real) ≤ 1 := by norm_num
    have hmle : m ≤ n0 := Nat.le_max_right _ _
    have hpow : (3 / 4 : Real) ^ n0 ≤ (3 / 4 : Real) ^ m :=
      pow_le_pow_of_le_one hqNonneg hqLeOne hmle
    have hpowNonneg : 0 ≤ (3 / 4 : Real) ^ m := pow_nonneg hqNonneg _
    have hfirst : A * (3 / 4 : Real) ^ n0 ≤ A * (3 / 4 : Real) ^ m :=
      mul_le_mul_of_nonneg_left hpow hA
    have hsecond : A * (3 / 4 : Real) ^ m ≤
        (A + 1) * (3 / 4 : Real) ^ m := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact hpowNonneg
    have hthird : (A + 1) * (3 / 4 : Real) ^ m < (xiMultiplicity rho : Real) := by
      have := (lt_div_iff₀ hAplus).mp hm
      simpa [mul_comm] using this
    have hsmall : A * (3 / 4 : Real) ^ n0 < (xiMultiplicity rho : Real) :=
      (hfirst.trans hsecond).trans_lt hthird
    simpa only [A] using hsmall

/-- The fourth-order tail condition always yields one explicit dyadic
tail-sum bound.  The selected index is allowed to depend on the construction
threshold, but not on an individual spectral zero. -/
theorem exists_spectralTail_norm_shellSum_le_of_fourthOrderTail
    (F : CompactLogTest) (rho : Complex) (T epsilon : Real)
    (htail : FourthOrderSpectralTail F rho T epsilon) :
    ∃ n0 : Nat,
      (∑' m : Nat, ∑' sigma : spectralHeightShell (m + n0 + 1),
        ‖spectralTerm F sigma.1‖) ≤
        4 * epsilon ^ 2 * spectralMultiplicityConstant *
          (3 / 4 : Real) ^ n0 := by
  obtain ⟨n0, hT, hrhoHeight⟩ := exists_dyadic_tail_start T rho
  exact ⟨n0,
    spectralTail_norm_shellSum_le_of_fourthOrderTail
      F rho T epsilon htail n0 hT hrhoHeight⟩

end C1SpectralTailBound
end Source
end ConnesWeilRH
