/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaConstruction
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Finite nearby zeta zeros and finite Mellin interpolation

This module isolates the finite-dimensional part of the source Yoshida
construction. It proves that source nontrivial zeros in a closed ball form a
finite set and extends fixed-window Mellin interpolation from the six route
nodes to an arbitrary finite set of complex nodes.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20YoshidaNearZeros

open MeasureTheory
open Filter
open scoped Topology
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode

/-- The global source index set for a future spectral-side explicit formula. -/
def sourceNontrivialZeroSet : Set ℂ :=
  {z : ℂ | RHDefinitionBridge.standard.sourceNontrivialZero z}

theorem sourceNontrivialZeroSet_subset_riemannZetaZeros :
    sourceNontrivialZeroSet ⊆ riemannZetaZeros := by
  intro z hz
  exact
    RHDefinitionBridge.standard_mathlib_zeta_zero_of_source_nontrivial_zero
      z hz

theorem sourceNontrivialZero_re_lt_one
    {z : ℂ} (hz : RHDefinitionBridge.standard.sourceNontrivialZero z) :
    z.re < 1 := by
  apply lt_of_not_ge
  intro hre
  exact (riemannZeta_ne_zero_of_one_le_re hre) hz.zeta_zero

/-- Away from the explicit negative integers, the functional equation and the
zero-free right half-plane put every source nontrivial zero in `0 < re z`. -/
theorem sourceNontrivialZero_zero_lt_re_or_eq_neg_nat
    {z : ℂ} (hz : RHDefinitionBridge.standard.sourceNontrivialZero z) :
    0 < z.re ∨ ∃ n : Nat, z = -n := by
  by_cases hneg : ∃ n : Nat, z = -n
  · exact Or.inr hneg
  · left
    apply lt_of_not_ge
    intro hre
    have honeSubRe : 1 <= (1 - z).re := by
      change 1 <= 1 - z.re
      linarith
    have honeSubZero : riemannZeta (1 - z) = 0 := by
      rw [riemannZeta_one_sub (not_exists.mp hneg) hz.not_pole, hz.zeta_zero, mul_zero]
    exact (riemannZeta_ne_zero_of_one_le_re honeSubRe) honeSubZero

/-- Zeta has no zero at a negative odd integer. This is the missing half of
the trivial-zero classification needed to keep the source spectral index in
the open critical strip. -/
theorem riemannZeta_neg_two_mul_nat_add_one_ne_zero (k : ℕ) :
    riemannZeta (-(2 * k + 1 : ℕ)) ≠ 0 := by
  let s : ℂ := (2 * (k + 1 : ℕ) : ℕ)
  have hsRe : 1 ≤ s.re := by
    dsimp [s]
    push_cast
    have hkNonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hsGamma : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    dsimp [s]
    push_cast
    positivity
  have hsBase : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hsPower : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).2 (Or.inl hsBase)
  have hsCos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    have harg : (Real.pi : ℂ) * s / 2 =
        (((k + 1 : ℕ) : ℝ) * Real.pi : ℝ) := by
      dsimp [s]
      push_cast
      ring
    rw [harg, ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
    simp
  have hsNoNeg (n : ℕ) : s ≠ -n := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    push_cast at hre
    have hkPos : 0 < (k : ℝ) + 1 := by positivity
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsNeOne : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    push_cast at hre
    have hkPos : 0 < (k : ℝ) + 1 := by positivity
    linarith
  have hfe := riemannZeta_one_sub (s := s) hsNoNeg hsNeOne
  have hrhs :
      2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
          Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (mul_ne_zero two_ne_zero hsPower) hsGamma) hsCos)
      (riemannZeta_ne_zero_of_one_le_re hsRe)
  have honeSub : (1 : ℂ) - s = -(2 * k + 1 : ℕ) := by
    dsimp [s]
    push_cast
    ring
  rw [honeSub] at hfe
  rw [hfe]
  exact hrhs

/-- A source nontrivial zero cannot be any negative natural number: even
positive indices are precisely the excluded trivial zeros, odd indices are
nonzeros, and `zeta(0) = -1/2`. -/
theorem sourceNontrivialZero_not_eq_neg_nat
    {z : ℂ} (hz : RHDefinitionBridge.standard.sourceNontrivialZero z) :
    ¬∃ n : ℕ, z = -n := by
  rintro ⟨n, rfl⟩
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · subst n
    rcases k with _ | k
    · have hzeta := hz.zeta_zero
      norm_num [riemannZeta_zero] at hzeta
    · apply hz.not_negative_even
      exact ⟨k, by push_cast; ring⟩
  · subst n
    exact riemannZeta_neg_two_mul_nat_add_one_ne_zero k hz.zeta_zero

/-- Every source nontrivial zero lies strictly to the right of the imaginary
axis. Together with `sourceNontrivialZero_re_lt_one`, this places the spectral
index in the open critical strip and removes the spurious negative-integer
branch. -/
theorem sourceNontrivialZero_zero_lt_re
    {z : ℂ} (hz : RHDefinitionBridge.standard.sourceNontrivialZero z) :
    0 < z.re := by
  rcases sourceNontrivialZero_zero_lt_re_or_eq_neg_nat hz with hpos | hneg
  · exact hpos
  · exact False.elim (sourceNontrivialZero_not_eq_neg_nat hz hneg)

/-- The spectral index set is countable because it is a discrete subset of the
second-countable complex plane. -/
theorem sourceNontrivialZeroSet_countable :
    sourceNontrivialZeroSet.Countable := by
  have hLindelof : IsLindelof sourceNontrivialZeroSet :=
    isLindelof_iff_lindelofSpace.mpr inferInstance
  have hDiscrete : IsDiscrete sourceNontrivialZeroSet :=
    isDiscrete_riemannZetaZeros.mono
      sourceNontrivialZeroSet_subset_riemannZetaZeros
  exact IsLindelof.countable_of_isDiscrete hLindelof hDiscrete

/-- An `O(R log R)` dyadic shell-count bound turns quadratic pointwise decay
into absolute summability. The shell partition and its cardinality estimate
are the only inputs that a future zeta-zero counting theorem must provide. -/
theorem summable_of_dyadic_shell_card_bound
    {alpha : Type*} (f : alpha -> Real) (shell : Nat -> Set alpha)
    (hf : forall x, 0 <= f x)
    (hpartition : forall x, ExistsUnique (fun n => x ∈ shell n))
    (hfinite : forall n, (shell n).Finite)
    {K B : Real} (hB : 0 <= B)
    (hcard : forall n, ((shell n).ncard : Real) <=
      K * ((n + 1 : Nat) : Real) * (2 : Real) ^ n)
    (hpoint : forall n (x : shell n),
      f x <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f := by
  rw [summable_partition hf hpartition]
  constructor
  · intro n
    letI := (hfinite n).fintype
    exact (hasSum_fintype (fun x : shell n => f x)).summable
  · have hlinearGeometric : Summable (fun n : Nat =>
        ((n + 1 : Nat) : Real) * ((1 : Real) / 2) ^ n) := by
      have hn : Summable (fun n : Nat =>
          (n : Real) * ((1 : Real) / 2) ^ n) := by
        simpa using summable_pow_mul_geometric_of_norm_lt_one (R := Real) 1
          (show ‖(1 : Real) / 2‖ < 1 by norm_num)
      convert hn.add summable_geometric_two using 1
      ext n
      push_cast
      ring
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun x => hf x) ?_
      (hlinearGeometric.mul_left (K * B))
    intro n
    letI := (hfinite n).fintype
    rw [tsum_fintype]
    calc
      (∑ x : shell n, f x) <=
          ∑ _x : shell n, B / ((2 : Real) ^ n) ^ 2 := by
            exact Finset.sum_le_sum fun x _hx => hpoint n x
      _ = ((shell n).ncard : Real) *
          (B / ((2 : Real) ^ n) ^ 2) := by
            simp [Set.ncard, nsmul_eq_mul]
      _ <= (K * ((n + 1 : Nat) : Real) * (2 : Real) ^ n) *
          (B / ((2 : Real) ^ n) ^ 2) := by
            exact mul_le_mul_of_nonneg_right (hcard n) (div_nonneg hB (sq_nonneg _))
      _ = K * B * (((n + 1 : Nat) : Real) * ((1 : Real) / 2) ^ n) := by
            field_simp
            calc
              K * B = K * B * ((2 : Real) * ((1 : Real) / 2)) ^ n := by
                norm_num
              _ = K * (2 : Real) ^ n * B * ((1 : Real) / 2) ^ n := by
                rw [mul_pow]
                ring

/-- A geometric shell-count bound with ratio strictly below `4` turns
quadratic dyadic pointwise decay into absolute summability. This is the actual
growth threshold needed by the spectral tail; the `O(R log R)` specialization
above is stronger than necessary. -/
theorem summable_of_geometric_shell_card_bound
    {alpha : Type*} (f : alpha -> Real) (shell : Nat -> Set alpha)
    (hf : forall x, 0 <= f x)
    (hpartition : forall x, ExistsUnique (fun n => x ∈ shell n))
    (hfinite : forall n, (shell n).Finite)
    {K B q : Real} (hB : 0 <= B) (hq : 0 <= q) (hq4 : q < 4)
    (hcard : forall n, ((shell n).ncard : Real) <= K * q ^ n)
    (hpoint : forall n (x : shell n),
      f x <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f := by
  rw [summable_partition hf hpartition]
  constructor
  · intro n
    letI := (hfinite n).fintype
    exact (hasSum_fintype (fun x : shell n => f x)).summable
  · have hratioNonneg : 0 <= q / 4 := div_nonneg hq (by norm_num)
    have hratioLt : q / 4 < 1 := (div_lt_one (by norm_num : (0 : Real) < 4)).mpr hq4
    have hgeometric : Summable (fun n : Nat => (q / 4) ^ n) :=
      summable_geometric_of_lt_one hratioNonneg hratioLt
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun x => hf x) ?_
      (hgeometric.mul_left (K * B))
    intro n
    letI := (hfinite n).fintype
    rw [tsum_fintype]
    calc
      (∑ x : shell n, f x) <=
          ∑ _x : shell n, B / ((2 : Real) ^ n) ^ 2 := by
            exact Finset.sum_le_sum fun x _hx => hpoint n x
      _ = ((shell n).ncard : Real) *
          (B / ((2 : Real) ^ n) ^ 2) := by
            simp [Set.ncard, nsmul_eq_mul]
      _ <= (K * q ^ n) * (B / ((2 : Real) ^ n) ^ 2) := by
            exact mul_le_mul_of_nonneg_right (hcard n) (div_nonneg hB (sq_nonneg _))
      _ = K * B * (q / 4) ^ n := by
            rw [div_pow]
            norm_num [pow_two, mul_pow]
            have hfour : (2 : Real) ^ n * (2 : Real) ^ n = 4 ^ n := by
              rw [← mul_pow]
              norm_num
            rw [hfour]
            ring

theorem exists_lt_two_pow_succ (r : Real) :
    ∃ n : Nat, r < (2 : Real) ^ (n + 1) := by
  have heventually :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : Real) < 2 by norm_num)).eventually_gt_atTop r
  rcases (eventually_atTop.1 heventually) with ⟨N, hN⟩
  exact ⟨N, hN (N + 1) (Nat.le_succ N)⟩

/-- The least dyadic radius `2^(n+1)` strictly larger than `r`. -/
noncomputable def dyadicShellIndex (r : Real) : Nat :=
  Nat.find (exists_lt_two_pow_succ r)

theorem lt_two_pow_succ_dyadicShellIndex (r : Real) :
    r < (2 : Real) ^ (dyadicShellIndex r + 1) :=
  Nat.find_spec (exists_lt_two_pow_succ r)

theorem pow_succ_le_of_dyadicShellIndex_eq_succ
    {r : Real} {n : Nat} (hindex : dyadicShellIndex r = n + 1) :
    (2 : Real) ^ (n + 1) <= r := by
  apply le_of_not_gt
  intro hr
  have hminimal := Nat.find_min' (exists_lt_two_pow_succ r) hr
  rw [← dyadicShellIndex, hindex] at hminimal
  omega

def sourceNontrivialZerosInClosedBall (rho : ℂ) (R : ℝ) : Set ℂ :=
  Metric.closedBall rho R ∩
    sourceNontrivialZeroSet

theorem sourceNontrivialZerosInClosedBall_finite (rho : ℂ) (R : ℝ) :
    (sourceNontrivialZerosInClosedBall rho R).Finite := by
  have hcompact : IsCompact (Metric.closedBall rho R) :=
    isCompact_closedBall rho R
  apply (hcompact.inter_riemannZetaZeros_finite).subset
  intro z hz
  exact ⟨hz.1,
    sourceNontrivialZeroSet_subset_riemannZetaZeros hz.2⟩

/-- Source nontrivial zeros grouped by their least strict dyadic radius around
`rho`. The zero-th shell contains the radius-two closed neighborhood. -/
noncomputable def sourceNontrivialZeroDyadicShell
    (rho : ℂ) (n : Nat) : Set sourceNontrivialZeroSet :=
  {z | dyadicShellIndex (dist z.1 rho) = n}

theorem sourceNontrivialZeroDyadicShell_partition (rho : ℂ) :
    forall z : sourceNontrivialZeroSet,
      ExistsUnique (fun n => z ∈ sourceNontrivialZeroDyadicShell rho n) := by
  intro z
  refine ⟨dyadicShellIndex (dist z.1 rho), ?_, ?_⟩
  · rfl
  · intro n hn
    exact hn.symm

theorem sourceNontrivialZeroDyadicShell_finite (rho : ℂ) (n : Nat) :
    (sourceNontrivialZeroDyadicShell rho n).Finite := by
  let e : sourceNontrivialZeroSet ↪ ℂ := Function.Embedding.subtype _
  have hpreimage :
      (e ⁻¹' sourceNontrivialZerosInClosedBall rho ((2 : Real) ^ (n + 1))).Finite :=
    Set.Finite.preimage_embedding e
      (sourceNontrivialZerosInClosedBall_finite rho ((2 : Real) ^ (n + 1)))
  apply hpreimage.subset
  intro z hz
  change dyadicShellIndex (dist z.1 rho) = n at hz
  change z.1 ∈ sourceNontrivialZerosInClosedBall rho ((2 : Real) ^ (n + 1))
  refine ⟨?_, z.2⟩
  rw [Metric.mem_closedBall]
  rw [← hz] at *
  exact (lt_two_pow_succ_dyadicShellIndex (dist z.1 rho)).le

/-- The symmetric-height source zero set matching the `N-bar(T)` counting
function in Hasanalizade--Shen--Wong. -/
def sourceNontrivialZerosInSymmetricHeight (T : ℝ) :
    Set sourceNontrivialZeroSet :=
  {z | |z.1.im| ≤ T}

theorem sourceNontrivialZerosInSymmetricHeight_finite (T : ℝ) :
    (sourceNontrivialZerosInSymmetricHeight T).Finite := by
  let e : sourceNontrivialZeroSet ↪ ℂ := Function.Embedding.subtype _
  have hpreimage :
      (e ⁻¹' sourceNontrivialZerosInClosedBall 0 (1 + T)).Finite :=
    Set.Finite.preimage_embedding e
      (sourceNontrivialZerosInClosedBall_finite 0 (1 + T))
  apply hpreimage.subset
  intro z hz
  change |z.1.im| ≤ T at hz
  change z.1 ∈ sourceNontrivialZerosInClosedBall 0 (1 + T)
  refine ⟨?_, z.2⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply le_of_lt
  calc
    ‖z.1‖ ≤ |z.1.re| + |z.1.im| := Complex.norm_le_abs_re_add_abs_im z.1
    _ < 1 + |z.1.im| := by
      rw [abs_of_pos (sourceNontrivialZero_zero_lt_re z.2)]
      linarith [sourceNontrivialZero_re_lt_one z.2]
    _ ≤ 1 + T := by linarith

/-- A shell around an arbitrary selected zero lies in the symmetric-height
window obtained by adding the shell radius to the center height. -/
theorem sourceNontrivialZeroDyadicShell_subset_symmetricHeight
    (rho : ℂ) (n : Nat) :
    sourceNontrivialZeroDyadicShell rho n ⊆
      sourceNontrivialZerosInSymmetricHeight
        (|rho.im| + (2 : ℝ) ^ (n + 1)) := by
  intro z hz
  change dyadicShellIndex (dist z.1 rho) = n at hz
  change |z.1.im| ≤ |rho.im| + (2 : ℝ) ^ (n + 1)
  have hdist : dist z.1 rho ≤ (2 : ℝ) ^ (n + 1) := by
    rw [← hz]
    exact (lt_two_pow_succ_dyadicShellIndex (dist z.1 rho)).le
  calc
    |z.1.im| = |(z.1 - rho).im + rho.im| := by
      congr 1
      simp
    _ ≤ |(z.1 - rho).im| + |rho.im| := abs_add_le _ _
    _ ≤ ‖z.1 - rho‖ + |rho.im| := by
      linarith [Complex.abs_im_le_norm (z.1 - rho)]
    _ = |rho.im| + dist z.1 rho := by rw [dist_eq_norm]; ring
    _ ≤ |rho.im| + (2 : ℝ) ^ (n + 1) := by linarith

theorem sourceNontrivialZeroDyadicShell_ncard_le_symmetricHeight
    (rho : ℂ) (n : Nat) :
    (sourceNontrivialZeroDyadicShell rho n).ncard ≤
      (sourceNontrivialZerosInSymmetricHeight
        (|rho.im| + (2 : ℝ) ^ (n + 1))).ncard :=
  Set.ncard_le_ncard
    (sourceNontrivialZeroDyadicShell_subset_symmetricHeight rho n)
    (sourceNontrivialZerosInSymmetricHeight_finite _)

/-- For source nontrivial zeros, an `O(R log R)` dyadic counting estimate and a
quadratic dyadic majorant are sufficient for spectral absolute summability. -/
theorem sourceNontrivialZero_summable_of_dyadic_bounds
    (rho : ℂ) (f : sourceNontrivialZeroSet -> Real)
    (hf : forall z, 0 <= f z) {K B : Real} (hB : 0 <= B)
    (hcard : forall n,
      ((sourceNontrivialZeroDyadicShell rho n).ncard : Real) <=
        K * ((n + 1 : Nat) : Real) * (2 : Real) ^ n)
    (hpoint : forall n (z : sourceNontrivialZeroDyadicShell rho n),
      f z <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f :=
  summable_of_dyadic_shell_card_bound f
    (sourceNontrivialZeroDyadicShell rho) hf
    (sourceNontrivialZeroDyadicShell_partition rho)
    (sourceNontrivialZeroDyadicShell_finite rho) hB hcard hpoint

/-- The source-zero specialization of the sharp geometric threshold. Any
dyadic shell growth ratio below `4` is compatible with quadratic spectral
decay. -/
theorem sourceNontrivialZero_summable_of_geometric_dyadic_bounds
    (rho : ℂ) (f : sourceNontrivialZeroSet -> Real)
    (hf : forall z, 0 <= f z) {K B q : Real}
    (hB : 0 <= B) (hq : 0 <= q) (hq4 : q < 4)
    (hcard : forall n,
      ((sourceNontrivialZeroDyadicShell rho n).ncard : Real) <= K * q ^ n)
    (hpoint : forall n (z : sourceNontrivialZeroDyadicShell rho n),
      f z <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f :=
  summable_of_geometric_shell_card_bound f
    (sourceNontrivialZeroDyadicShell rho) hf
    (sourceNontrivialZeroDyadicShell_partition rho)
    (sourceNontrivialZeroDyadicShell_finite rho) hB hq hq4 hcard hpoint

/-- The sharp geometric consumer stated with the symmetric-height counting
function used by the Jensen reduction. -/
theorem sourceNontrivialZero_summable_of_symmetricHeight_geometric_bounds
    (rho : ℂ) (f : sourceNontrivialZeroSet -> Real)
    (hf : forall z, 0 <= f z) {K B q : Real}
    (hB : 0 <= B) (hq : 0 <= q) (hq4 : q < 4)
    (hcount : forall n,
      ((sourceNontrivialZerosInSymmetricHeight
        (|rho.im| + (2 : Real) ^ (n + 1))).ncard : Real) <= K * q ^ n)
    (hpoint : forall n (z : sourceNontrivialZeroDyadicShell rho n),
      f z <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f := by
  apply sourceNontrivialZero_summable_of_geometric_dyadic_bounds
    rho f hf hB hq hq4
  · intro n
    calc
      ((sourceNontrivialZeroDyadicShell rho n).ncard : Real) <=
          ((sourceNontrivialZerosInSymmetricHeight
            (|rho.im| + (2 : Real) ^ (n + 1))).ncard : Real) := by
              exact_mod_cast
                sourceNontrivialZeroDyadicShell_ncard_le_symmetricHeight rho n
      _ <= K * q ^ n := hcount n
  · exact hpoint

/-- The summability consumer stated directly with the symmetric zero-counting
function used by the source Riemann--von Mangoldt estimate. -/
theorem sourceNontrivialZero_summable_of_symmetricHeight_dyadic_bounds
    (rho : ℂ) (f : sourceNontrivialZeroSet -> Real)
    (hf : forall z, 0 <= f z) {K B : Real} (hB : 0 <= B)
    (hcount : forall n,
      ((sourceNontrivialZerosInSymmetricHeight
        (|rho.im| + (2 : Real) ^ (n + 1))).ncard : Real) <=
          K * ((n + 1 : Nat) : Real) * (2 : Real) ^ n)
    (hpoint : forall n (z : sourceNontrivialZeroDyadicShell rho n),
      f z <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f := by
  apply sourceNontrivialZero_summable_of_dyadic_bounds rho f hf hB
  · intro n
    calc
      ((sourceNontrivialZeroDyadicShell rho n).ncard : Real) ≤
          ((sourceNontrivialZerosInSymmetricHeight
            (|rho.im| + (2 : Real) ^ (n + 1))).ncard : Real) := by
              exact_mod_cast
                sourceNontrivialZeroDyadicShell_ncard_le_symmetricHeight rho n
      _ ≤ K * ((n + 1 : Nat) : Real) * (2 : Real) ^ n := hcount n
  · exact hpoint

/-- A global `A * T * log T + C * T` bound for the symmetric source zero count
implies the dyadic estimate required by the spectral summability consumer. -/
theorem sourceNontrivialZerosInSymmetricHeight_dyadic_bound_of_linear_log_bound
    (rho : ℂ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      ((sourceNontrivialZerosInSymmetricHeight T).ncard : ℝ) ≤
        A * T * Real.log T + C * T) :
    ∀ n : Nat,
      ((sourceNontrivialZerosInSymmetricHeight
        (|rho.im| + (2 : ℝ) ^ (n + 1))).ncard : ℝ) ≤
          ((|rho.im| + 2) *
              (A * (Real.log (|rho.im| + 2) + Real.log 2) + C)) *
            ((n + 1 : Nat) : ℝ) * (2 : ℝ) ^ n := by
  intro n
  let H : ℝ := |rho.im|
  let T : ℝ := H + (2 : ℝ) ^ (n + 1)
  have hH : 0 ≤ H := abs_nonneg _
  have hpowOne : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hTOne : 1 ≤ T := by
    dsimp [T]
    have hpowTwo : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith
    linarith
  have hHtwoPos : 0 < H + 2 := by linarith
  have hTPos : 0 < T := lt_of_lt_of_le zero_lt_one hTOne
  have hTUpper : T ≤ (H + 2) * (2 : ℝ) ^ n := by
    dsimp [T]
    rw [pow_succ]
    nlinarith
  have hlogUpper : Real.log T ≤
      (n + 1 : ℝ) * (Real.log (H + 2) + Real.log 2) := by
    calc
      Real.log T ≤ Real.log ((H + 2) * (2 : ℝ) ^ n) :=
        Real.log_le_log hTPos hTUpper
      _ = Real.log (H + 2) + (n : ℝ) * Real.log 2 := by
        rw [Real.log_mul hHtwoPos.ne' (pow_ne_zero _ (by norm_num)), Real.log_pow]
      _ ≤ (n + 1 : ℝ) * (Real.log (H + 2) + Real.log 2) := by
        have hlogH : 0 ≤ Real.log (H + 2) := Real.log_nonneg (by linarith)
        have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        nlinarith
  have hlogNonneg : 0 ≤ Real.log T := Real.log_nonneg hTOne
  have hlinearLog :
      A * T * Real.log T + C * T ≤
        ((H + 2) *
            (A * (Real.log (H + 2) + Real.log 2) + C)) *
          ((n + 1 : Nat) : ℝ) * (2 : ℝ) ^ n := by
    have hnOne : (1 : ℝ) ≤ (n + 1 : Nat) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hlogFactor : 0 ≤ Real.log (H + 2) + Real.log 2 := by
      exact add_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
    calc
      A * T * Real.log T + C * T ≤
          A * ((H + 2) * (2 : ℝ) ^ n) *
              ((n + 1 : ℝ) * (Real.log (H + 2) + Real.log 2)) +
            C * ((H + 2) * (2 : ℝ) ^ n) := by
              gcongr
      _ = ((H + 2) *
            (A * (Real.log (H + 2) + Real.log 2) + C)) *
          ((n + 1 : Nat) : ℝ) * (2 : ℝ) ^ n -
          C * (H + 2) * ((n : ℝ) * (2 : ℝ) ^ n) := by
            push_cast
            ring
      _ ≤ ((H + 2) *
            (A * (Real.log (H + 2) + Real.log 2) + C)) *
          ((n + 1 : Nat) : ℝ) * (2 : ℝ) ^ n := by
            have : 0 ≤ C * (H + 2) * ((n : ℝ) * (2 : ℝ) ^ n) := by positivity
            linarith
  change ((sourceNontrivialZerosInSymmetricHeight T).ncard : ℝ) ≤ _
  change _ ≤ ((H + 2) *
      (A * (Real.log (H + 2) + Real.log 2) + C)) *
    ((n + 1 : Nat) : ℝ) * (2 : ℝ) ^ n
  exact (hcount T hTOne).trans hlinearLog

/-- The spectral summability theorem with the source counting input reduced to
one standard global Riemann--von Mangoldt growth inequality. -/
theorem sourceNontrivialZero_summable_of_linear_log_count_bound
    (rho : ℂ) (f : sourceNontrivialZeroSet -> Real)
    (hf : forall z, 0 <= f z) {A C B : Real}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      ((sourceNontrivialZerosInSymmetricHeight T).ncard : ℝ) ≤
        A * T * Real.log T + C * T)
    (hpoint : forall n (z : sourceNontrivialZeroDyadicShell rho n),
      f z <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f :=
  sourceNontrivialZero_summable_of_symmetricHeight_dyadic_bounds rho f hf hB
    (sourceNontrivialZerosInSymmetricHeight_dyadic_bound_of_linear_log_bound
      rho hA hC hcount)
    hpoint

noncomputable def sourceNontrivialZerosInClosedBallFinset
    (rho : ℂ) (R : ℝ) : Finset ℂ :=
  (sourceNontrivialZerosInClosedBall_finite rho R).toFinset

@[simp] theorem mem_sourceNontrivialZerosInClosedBallFinset
    {rho z : ℂ} {R : ℝ} :
    z ∈ sourceNontrivialZerosInClosedBallFinset rho R ↔
      z ∈ Metric.closedBall rho R ∧
        RHDefinitionBridge.standard.sourceNontrivialZero z := by
  rw [sourceNontrivialZerosInClosedBallFinset, Set.Finite.mem_toFinset]
  rfl

abbrev FiniteMellinNode (nodes : Finset ℂ) := {z : ℂ // z ∈ nodes}

noncomputable def finiteMellinVector
    (nodes : Finset ℂ) (p : PositiveIntervalCompactTest) :
    FiniteMellinNode nodes → ℂ :=
  fun z => normalizedCC20TestSpace.mellinAt p.test z.1

noncomputable def windowedFiniteMellinVector
    (nodes : Finset ℂ) (a b : ℝ)
    (p : WindowedPositiveIntervalCompactTest a b) :
    FiniteMellinNode nodes → ℂ :=
  finiteMellinVector nodes p.1

noncomputable def finiteWeightedMellinKernel
    (nodes : Finset ℂ) (coeff : FiniteMellinNode nodes → ℂ)
    (t : ℝ) : ℂ :=
  ∑ z : FiniteMellinNode nodes, coeff z * (t : ℂ) ^ (z.1 - 1)

noncomputable def finiteExpMomentSum
    {nodes : Finset ℂ} (coeff : FiniteMellinNode nodes → ℂ)
    (n : ℕ) (u : ℝ) : ℂ :=
  ∑ z : FiniteMellinNode nodes,
    coeff z * (z.1 - 1) ^ n * Complex.exp ((z.1 - 1) * (u : ℂ))

theorem finiteWeightedMellinKernel_exp_eq_finiteExpMomentSum_zero
    (nodes : Finset ℂ) (coeff : FiniteMellinNode nodes → ℂ) (u : ℝ) :
    finiteWeightedMellinKernel nodes coeff (Real.exp u) =
      finiteExpMomentSum coeff 0 u := by
  unfold finiteWeightedMellinKernel finiteExpMomentSum
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [pow_zero, mul_one]
  congr 1
  rw [Complex.cpow_def_of_ne_zero]
  · rw [Complex.ofReal_exp, Complex.log_exp]
    · ring_nf
    · simpa using Real.pi_pos
    · simpa using Real.pi_nonneg
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)

theorem hasDerivAt_finiteExpMomentSum
    {nodes : Finset ℂ} (coeff : FiniteMellinNode nodes → ℂ)
    (n : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => finiteExpMomentSum coeff n x)
      (finiteExpMomentSum coeff (n + 1) u) u := by
  classical
  unfold finiteExpMomentSum
  refine HasDerivAt.fun_sum
    (u := (Finset.univ : Finset (FiniteMellinNode nodes))) ?_
  intro z _hz
  let exponent : ℂ := z.1 - 1
  have hlin : HasDerivAt (fun x : ℝ => exponent * (x : ℂ)) exponent u := by
    simpa using ((hasDerivAt_id (u : ℂ)).const_mul exponent).comp_ofReal
  have hexp :
      HasDerivAt (fun x : ℝ => Complex.exp (exponent * (x : ℂ)))
        (exponent * Complex.exp (exponent * (u : ℂ))) u := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp
  have hterm := hexp.const_mul (coeff z * exponent ^ n)
  simpa [exponent, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hterm

theorem finiteExpMomentSum_eq_zero_of_kernel_exp_eq_zero_on_Ioo
    {nodes : Finset ℂ} (coeff : FiniteMellinNode nodes → ℂ)
    {a b : ℝ}
    (hzero : ∀ u ∈ Set.Ioo a b,
      finiteWeightedMellinKernel nodes coeff (Real.exp u) = 0) :
    ∀ n : ℕ, ∀ u ∈ Set.Ioo a b,
      finiteExpMomentSum coeff n u = 0 := by
  intro n
  induction n with
  | zero =>
      intro u hu
      rw [← finiteWeightedMellinKernel_exp_eq_finiteExpMomentSum_zero]
      exact hzero u hu
  | succ n ih =>
      intro u hu
      have hderiv := hasDerivAt_finiteExpMomentSum coeff n u
      have hconst :
          HasDerivAt (fun x : ℝ => finiteExpMomentSum coeff n x) 0 u := by
        apply (hasDerivAt_const (x := u) (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
        exact ih x hx
      exact hderiv.unique hconst

theorem finiteExpMomentSum_zero_at_zero_eq_power_sum
    {nodes : Finset ℂ} (coeff : FiniteMellinNode nodes → ℂ) (n : ℕ) :
    finiteExpMomentSum coeff n 0 =
      ∑ z : FiniteMellinNode nodes, coeff z * (z.1 - 1) ^ n := by
  unfold finiteExpMomentSum
  refine Finset.sum_congr rfl ?_
  intro z _
  simp [mul_comm, mul_left_comm]

/-- Distinct finite complex nodes give linearly independent Mellin kernels on
every log window containing zero. -/
theorem finiteWeightedMellinKernel_log_window_independence
    (nodes : Finset ℂ) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (coeff : FiniteMellinNode nodes → ℂ)
    (hzero : ∀ u ∈ Set.Ioo a b,
      finiteWeightedMellinKernel nodes coeff (Real.exp u) = 0) :
    coeff = 0 := by
  classical
  let alpha := FiniteMellinNode nodes
  let e : Fin (Fintype.card alpha) ≃ alpha := (Fintype.equivFin alpha).symm
  have hmom : ∀ n : ℕ,
      (∑ z : alpha, coeff z * (z.1 - 1) ^ n) = 0 := by
    intro n
    have h := finiteExpMomentSum_eq_zero_of_kernel_exp_eq_zero_on_Ioo
      coeff hzero n 0 ⟨ha, hb⟩
    rwa [finiteExpMomentSum_zero_at_zero_eq_power_sum] at h
  have hinj : Function.Injective
      (fun i : Fin (Fintype.card alpha) => (e i).1 - 1) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    have h := congrArg (fun w : ℂ => w + 1) hij
    simpa [sub_eq_add_neg, add_assoc] using h
  let v : Fin (Fintype.card alpha) → ℂ := fun i => coeff (e i)
  have hvzero : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := fun i : Fin (Fintype.card alpha) => (e i).1 - 1)
      (v := v) hinj
    intro n
    have hn := hmom (n : ℕ)
    change
      (∑ j : Fin (Fintype.card alpha),
        v j * ((e j).1 - 1) ^ (n : ℕ)) = 0
    rw [show
      (∑ j : Fin (Fintype.card alpha),
        v j * ((e j).1 - 1) ^ (n : ℕ)) =
          ∑ z : alpha, coeff z * (z.1 - 1) ^ (n : ℕ) by
        dsimp [v]
        exact Equiv.sum_comp e
          (fun z : alpha => coeff z * (z.1 - 1) ^ (n : ℕ))]
    exact hn
  funext z
  obtain ⟨i, rfl⟩ := e.surjective z
  exact congrFun hvzero i

theorem continuousAt_finiteWeightedMellinKernel_of_pos
    (nodes : Finset ℂ) (coeff : FiniteMellinNode nodes → ℂ)
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun x : ℝ => finiteWeightedMellinKernel nodes coeff x) t := by
  classical
  unfold finiteWeightedMellinKernel
  refine tendsto_finsetSum (Finset.univ : Finset (FiniteMellinNode nodes)) ?_
  intro z _hz
  exact continuousAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const t (z.1 - 1) (Or.inr ht.ne'))

theorem finiteWeightedMellinKernel_phase_re_pos_at_point
    (nodes : Finset ℂ) (coeff : FiniteMellinNode nodes → ℂ) {t : ℝ}
    (hne : finiteWeightedMellinKernel nodes coeff t ≠ 0) :
    0 < ((star (finiteWeightedMellinKernel nodes coeff t)) *
      finiteWeightedMellinKernel nodes coeff t).re := by
  have hnorm :
      0 < Complex.normSq (finiteWeightedMellinKernel nodes coeff t) :=
    Complex.normSq_pos.mpr hne
  have hnormRe :
      0 < ((Complex.normSq (finiteWeightedMellinKernel nodes coeff t) : ℂ).re) := by
    simpa using hnorm
  rw [Complex.normSq_eq_conj_mul_self] at hnormRe
  simpa using hnormRe

theorem finiteWeightedMellinKernel_phase_re_positive_interval
    (nodes : Finset ℂ) (coeff : FiniteMellinNode nodes → ℂ) {t : ℝ}
    (ht : 0 < t) (hne : finiteWeightedMellinKernel nodes coeff t ≠ 0) :
    ∃ a b : ℝ,
      0 < a ∧ a < t ∧ t < b ∧
      ∀ x ∈ Set.Ioo a b,
        0 < ((star (finiteWeightedMellinKernel nodes coeff t)) *
          finiteWeightedMellinKernel nodes coeff x).re := by
  let phase : ℂ := star (finiteWeightedMellinKernel nodes coeff t)
  have hpos :
      0 < (phase * finiteWeightedMellinKernel nodes coeff t).re := by
    simpa [phase] using
      finiteWeightedMellinKernel_phase_re_pos_at_point nodes coeff hne
  have hcont : ContinuousAt
      (fun x : ℝ =>
        (phase * finiteWeightedMellinKernel nodes coeff x).re) t :=
    Complex.continuous_re.continuousAt.comp
      (continuousAt_const.mul
        (continuousAt_finiteWeightedMellinKernel_of_pos nodes coeff ht))
  have hevent : ∀ᶠ x in 𝓝 t,
      0 < (phase * finiteWeightedMellinKernel nodes coeff x).re :=
    hcont.eventually (isOpen_Ioi.mem_nhds hpos)
  rcases Filter.Eventually.exists_Ioo_subset hevent with
    ⟨a, b, htIoo, hIoo⟩
  refine ⟨max a (t / 2), b, lt_max_of_lt_right (half_pos ht),
    max_lt htIoo.1 (half_lt_self ht), htIoo.2, ?_⟩
  intro x hx
  have hxIoo : x ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_lt (le_max_left a (t / 2)) hx.1, hx.2⟩
  simpa [phase] using hIoo hxIoo

theorem integrableOn_finiteWeightedMellinKernel_mul_test
    (nodes : Finset ℂ) (coeff : FiniteMellinNode nodes → ℂ)
    (p : PositiveIntervalCompactTest) :
    IntegrableOn
      (fun x : ℝ =>
        finiteWeightedMellinKernel nodes coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
      (Set.Ioi 0) := by
  let f : TestFunction :=
    normalizedCC20ConcreteTestAlgebra.legacy.encode p.test
  have hsum : IntegrableOn
      (fun x : ℝ =>
        ∑ z : FiniteMellinNode nodes,
          (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x))
      (Set.Ioi 0) := by
    apply integrable_finsetSum
    intro z _hz
    have hzconv : MellinConvergent (fun x : ℝ => f x) z.1 :=
      testFunction_mellinConvergent_of_support_subset_Icc
        f z.1 p.lower_pos p.support_subset
    exact hzconv.const_smul (coeff z)
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr hsum
  intro x _hx
  change
    finiteWeightedMellinKernel nodes coeff x *
        normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x =
      ∑ z : FiniteMellinNode nodes,
        (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x)
  rw [finiteWeightedMellinKernel, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro z _hz
  simp [f, SchwartzMap.smul_apply, smul_eq_mul]
  ring

theorem finiteWeightedMellinKernel_phase_integral_re_eq
    (nodes : Finset ℂ) (coeff : FiniteMellinNode nodes → ℂ)
    (p : PositiveIntervalCompactTest) (phase : ℂ) :
    (phase *
        (∫ x : ℝ in Set.Ioi 0,
          finiteWeightedMellinKernel nodes coeff x *
            normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)).re =
      ∫ x : ℝ in Set.Ioi 0,
        (phase *
          (finiteWeightedMellinKernel nodes coeff x *
            normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)).re := by
  let h : ℝ → ℂ := fun x =>
    finiteWeightedMellinKernel nodes coeff x *
      normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x
  have hh : IntegrableOn h (Set.Ioi 0) :=
    integrableOn_finiteWeightedMellinKernel_mul_test nodes coeff p
  have hphase : Integrable (fun x => phase * h x)
      (volume.restrict (Set.Ioi 0)) :=
    hh.integrable.const_mul phase
  change
    (phase * (∫ x : ℝ in Set.Ioi 0, h x)).re =
      ∫ x : ℝ in Set.Ioi 0, (phase * h x).re
  rw [← integral_const_mul]
  exact (Complex.reCLM.integral_comp_comm hphase).symm

theorem exists_windowed_test_with_finite_kernel_integral_ne_zero
    (nodes : Finset ℂ) {a b : ℝ}
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (coeff : FiniteMellinNode nodes → ℂ) (hcoeff : coeff ≠ 0) :
    ∃ p : PositiveIntervalCompactTest,
      p.IsSupportedIn a b ∧
      (∫ x : ℝ in Set.Ioi 0,
        finiteWeightedMellinKernel nodes coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ≠ 0 := by
  have hlog_a : Real.log a < 0 := by
    rw [Real.log_lt_iff_lt_exp ha, Real.exp_zero]
    exact ha_one
  have hlog_b : 0 < Real.log b := Real.log_pos hone_b
  have hpoint : ∃ t ∈ Set.Ioo a b,
      finiteWeightedMellinKernel nodes coeff t ≠ 0 := by
    by_contra hnone
    apply hcoeff
    apply finiteWeightedMellinKernel_log_window_independence
      nodes hlog_a hlog_b coeff
    intro u hu
    by_contra hne
    apply hnone
    refine ⟨Real.exp u, ?_, hne⟩
    exact ⟨(Real.log_lt_iff_lt_exp ha).mp hu.1,
      (Real.lt_log_iff_exp_lt (lt_trans zero_lt_one hone_b)).mp hu.2⟩
  rcases hpoint with ⟨t, ht, htne⟩
  have htpos : 0 < t := ha.trans ht.1
  rcases finiteWeightedMellinKernel_phase_re_positive_interval
      nodes coeff htpos htne with
    ⟨localA, localB, hlocalA_pos, hlocalA_t, ht_localB, hphase_pos⟩
  let clippedA : ℝ := max localA a
  let clippedB : ℝ := min localB b
  have hclippedA_pos : 0 < clippedA := lt_max_of_lt_right ha
  have hclippedA_t : clippedA < t := max_lt hlocalA_t ht.1
  have ht_clippedB : t < clippedB := lt_min ht_localB ht.2
  have hphase_clipped : ∀ x ∈ Set.Ioo clippedA clippedB,
      0 < ((star (finiteWeightedMellinKernel nodes coeff t)) *
        finiteWeightedMellinKernel nodes coeff x).re := by
    intro x hx
    apply hphase_pos x
    exact ⟨lt_of_le_of_lt (le_max_left localA a) hx.1,
      lt_of_lt_of_le hx.2 (min_le_left localB b)⟩
  rcases exists_positive_interval_compact_test_real_bump
      hclippedA_t ht_clippedB hclippedA_pos with
    ⟨p, hsuppClipped, hnonneg, him, htone⟩
  let phase : ℂ := star (finiteWeightedMellinKernel nodes coeff t)
  let realIntegrand : ℝ → ℝ := fun x =>
    (phase *
      (finiteWeightedMellinKernel nodes coeff x *
        normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)).re
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioi 0)] realIntegrand := by
    refine Eventually.of_forall ?_
    intro x
    by_cases hxmem : x ∈ Function.support
        (fun y : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test y)
    · have hxIoo : x ∈ Set.Ioo clippedA clippedB := hsuppClipped hxmem
      have hxpos :
          0 < (phase * finiteWeightedMellinKernel nodes coeff x).re := by
        simpa [phase] using hphase_clipped x hxIoo
      have hmul : realIntegrand x =
          (phase * finiteWeightedMellinKernel nodes coeff x).re *
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x).re := by
        dsimp [realIntegrand]
        rw [← mul_assoc, Complex.mul_re]
        simp [him x]
      rw [hmul]
      exact mul_nonneg hxpos.le (hnonneg x)
    · have hbump_zero :
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x = 0 :=
        not_not.mp hxmem
      simp [realIntegrand, hbump_zero]
  have hint : Integrable realIntegrand (volume.restrict (Set.Ioi 0)) := by
    have hcomplex : Integrable
        (fun x : ℝ =>
          phase *
            (finiteWeightedMellinKernel nodes coeff x *
              normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x))
        (volume.restrict (Set.Ioi 0)) :=
      (integrableOn_finiteWeightedMellinKernel_mul_test nodes coeff p).integrable
        |>.const_mul phase
    exact hcomplex.re
  have hreal_at : 0 < realIntegrand t := by
    dsimp [realIntegrand]
    rw [htone]
    simpa [phase, mul_assoc] using
      finiteWeightedMellinKernel_phase_re_pos_at_point nodes coeff htne
  have hcont : ContinuousAt realIntegrand t := by
    have hkernel :=
      continuousAt_finiteWeightedMellinKernel_of_pos nodes coeff htpos
    have hphaseKernel : ContinuousAt
        (fun x : ℝ => phase * finiteWeightedMellinKernel nodes coeff x) t :=
      continuousAt_const.mul hkernel
    have hbump : ContinuousAt
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) t :=
      (SchwartzMap.continuous
        (normalizedCC20ConcreteTestAlgebra.legacy.encode p.test)).continuousAt
    have hcomplex : ContinuousAt
        (fun x : ℝ =>
          (phase * finiteWeightedMellinKernel nodes coeff x) *
            normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) t :=
      hphaseKernel.mul hbump
    simpa [realIntegrand, mul_assoc] using
      Complex.continuous_re.continuousAt.comp hcomplex
  have hsupport_pos :
      0 < (volume.restrict (Set.Ioi 0)) (Function.support realIntegrand) := by
    have hevent : ∀ᶠ x in 𝓝 t, 0 < realIntegrand x :=
      hcont.eventually (isOpen_Ioi.mem_nhds hreal_at)
    rcases Filter.Eventually.exists_Ioo_subset hevent with
      ⟨lower, upper, htIoo, hIoo⟩
    let positiveLower : ℝ := max lower (t / 2)
    have hlower_pos : 0 < positiveLower := lt_max_of_lt_right (half_pos htpos)
    have hlower_lt_t : positiveLower < t :=
      max_lt htIoo.1 (half_lt_self htpos)
    have hlower_lt_upper : positiveLower < upper :=
      lt_trans hlower_lt_t htIoo.2
    have hsubset : Set.Ioo positiveLower upper ⊆
        Function.support realIntegrand := by
      intro x hx
      rw [Function.mem_support]
      exact ne_of_gt (hIoo
        ⟨lt_of_le_of_lt (le_max_left lower (t / 2)) hx.1, hx.2⟩)
    have hinterval_pos :
        0 < (volume.restrict (Set.Ioi 0))
          (Set.Ioo positiveLower upper) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      have hinter : Set.Ioo positiveLower upper ∩ Set.Ioi 0 =
          Set.Ioo positiveLower upper := by
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, lt_trans hlower_pos hx.1⟩
      rw [hinter, Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlower_lt_upper)
    exact measure_pos_of_superset hsubset hinterval_pos.ne'
  have hpos : 0 < ∫ x : ℝ in Set.Ioi 0, realIntegrand x :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg_ae hint).2 hsupport_pos
  have hintegral :
      (∫ x : ℝ in Set.Ioi 0,
        finiteWeightedMellinKernel nodes coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ≠ 0 := by
    intro hzero
    have hphaseIntegral :=
      finiteWeightedMellinKernel_phase_integral_re_eq nodes coeff p phase
    rw [hzero] at hphaseIntegral
    simp only [mul_zero, Complex.zero_re] at hphaseIntegral
    rw [← hphaseIntegral] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨p, ?_, hintegral⟩
  intro x hx
  have hxClipped := hsuppClipped hx
  exact ⟨lt_of_le_of_lt (le_max_right localA a) hxClipped.1,
    lt_of_lt_of_le hxClipped.2 (min_le_right localB b)⟩

theorem finite_mellin_sum_eq_kernel_integral
    (nodes : Finset ℂ) (p : PositiveIntervalCompactTest)
    (coeff : FiniteMellinNode nodes → ℂ) :
    (∑ z : FiniteMellinNode nodes,
      finiteMellinVector nodes p z * coeff z) =
      ∫ x : ℝ in Set.Ioi 0,
        finiteWeightedMellinKernel nodes coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x := by
  let f : TestFunction :=
    normalizedCC20ConcreteTestAlgebra.legacy.encode p.test
  have hsum :
      (∑ z : FiniteMellinNode nodes,
        finiteMellinVector nodes p z * coeff z) =
        ∑ z : FiniteMellinNode nodes,
          ∫ x : ℝ in Set.Ioi 0,
            (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x) := by
    refine Finset.sum_congr rfl ?_
    intro z _hz
    rw [finiteMellinVector, normalizedCC20TestSpace_mellinAt_eq,
      normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]
    simpa [f, mellin, SchwartzMap.smul_apply, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using
      (mellin_const_smul
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
        z.1 (coeff z)).symm
  rw [hsum]
  calc
    (∑ z : FiniteMellinNode nodes,
        ∫ x : ℝ in Set.Ioi 0,
          (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x)) =
        ∫ x : ℝ in Set.Ioi 0,
          ∑ z : FiniteMellinNode nodes,
            (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x) := by
      rw [integral_finsetSum]
      intro z _hz
      exact
        (testFunction_mellinConvergent_of_support_subset_Icc
          f z.1 p.lower_pos p.support_subset).const_smul (coeff z)
    _ = ∫ x : ℝ in Set.Ioi 0,
        finiteWeightedMellinKernel nodes coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x _hx
      change
        (∑ z : FiniteMellinNode nodes,
          (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x)) =
          (∑ z : FiniteMellinNode nodes,
            coeff z * (x : ℂ) ^ (z.1 - 1)) *
              normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro z _hz
      simp [f, SchwartzMap.smul_apply, smul_eq_mul]
      ring

theorem mellinAt_positiveIntervalCompactTestCombination
    (c : PositiveIntervalCompactTest →₀ ℂ) (z : ℂ) :
    normalizedCC20TestSpace.mellinAt
        (positiveIntervalCompactTestCombination c) z =
      c.sum fun p coefficient =>
        coefficient * normalizedCC20TestSpace.mellinAt p.test z := by
  let node : NodeValueImage z :=
    ⟨z, by
      unfold expandedNodeValueFinset
      apply Finset.mem_image.mpr
      exact
        ⟨CC20YoshidaExpandedMomentNode.targetRho, Finset.mem_univ _, rfl⟩⟩
  simpa [imageMellinVector, node] using
    imageMellinVector_positiveIntervalCompactTestCombination z c node

theorem windowedFiniteMellinVector_combination
    (nodes : Finset ℂ) {a b : ℝ}
    (c : WindowedPositiveIntervalCompactTest a b →₀ ℂ)
    (z : FiniteMellinNode nodes) :
    normalizedCC20TestSpace.mellinAt
        (windowedPositiveIntervalCompactTestCombination c) z.1 =
      c.sum fun p coefficient =>
        coefficient * windowedFiniteMellinVector nodes a b p z := by
  rw [windowedPositiveIntervalCompactTestCombination,
    mellinAt_positiveIntervalCompactTestCombination]
  simpa [windowedFiniteMellinVector, finiteMellinVector] using
    (Finsupp.sum_mapDomain_index_inj
      (s := c)
      (h := fun p coefficient =>
        coefficient * normalizedCC20TestSpace.mellinAt p.test z.1)
      Subtype.val_injective)

noncomputable def finiteLinearFunctionalCoordinates
    {nodes : Finset ℂ}
    (L : (FiniteMellinNode nodes → ℂ) →ₗ[ℂ] ℂ) :
    FiniteMellinNode nodes → ℂ := by
  classical
  exact fun z => L ((Pi.basisFun ℂ (FiniteMellinNode nodes)) z)

theorem finiteLinearFunctional_apply_eq_sum_coordinates
    {nodes : Finset ℂ}
    (L : (FiniteMellinNode nodes → ℂ) →ₗ[ℂ] ℂ)
    (v : FiniteMellinNode nodes → ℂ) :
    L v = ∑ z : FiniteMellinNode nodes,
      v z * finiteLinearFunctionalCoordinates L z := by
  classical
  let basis := Pi.basisFun ℂ (FiniteMellinNode nodes)
  calc
    L v = L (∑ z : FiniteMellinNode nodes,
        (basis.repr v) z • basis z) := by rw [basis.sum_repr v]
    _ = ∑ z : FiniteMellinNode nodes,
        v z * finiteLinearFunctionalCoordinates L z := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro z _hz
      rw [map_smul]
      change
        ((Pi.basisFun ℂ (FiniteMellinNode nodes)).repr v z) *
            L ((Pi.basisFun ℂ (FiniteMellinNode nodes)) z) =
          v z * finiteLinearFunctionalCoordinates L z
      rw [Pi.basisFun_repr]
      rfl

theorem finiteLinearFunctionalCoordinates_ne_zero
    {nodes : Finset ℂ}
    {L : (FiniteMellinNode nodes → ℂ) →ₗ[ℂ] ℂ}
    (hL : L ≠ 0) :
    finiteLinearFunctionalCoordinates L ≠ 0 := by
  intro hcoords
  apply hL
  apply LinearMap.ext
  intro v
  rw [finiteLinearFunctional_apply_eq_sum_coordinates]
  simp [hcoords]

theorem windowedFiniteMellinVector_span_top
    (nodes : Finset ℂ) {a b : ℝ}
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    Submodule.span ℂ
      (Set.range (windowedFiniteMellinVector nodes a b)) = ⊤ := by
  classical
  have hsep :
      ∀ L : (FiniteMellinNode nodes → ℂ) →ₗ[ℂ] ℂ,
        L ≠ 0 →
          ∃ p : WindowedPositiveIntervalCompactTest a b,
            L (windowedFiniteMellinVector nodes a b p) ≠ 0 := by
    intro L hL
    let coeff := finiteLinearFunctionalCoordinates L
    have hcoeff : coeff ≠ 0 :=
      finiteLinearFunctionalCoordinates_ne_zero hL
    rcases exists_windowed_test_with_finite_kernel_integral_ne_zero
        nodes ha ha_one hone_b coeff hcoeff with
      ⟨p, hsupp, hintegral⟩
    let windowed : WindowedPositiveIntervalCompactTest a b := ⟨p, hsupp⟩
    refine ⟨windowed, ?_⟩
    rw [finiteLinearFunctional_apply_eq_sum_coordinates]
    change
      (∑ z : FiniteMellinNode nodes,
        finiteMellinVector nodes p z * coeff z) ≠ 0
    rw [finite_mellin_sum_eq_kernel_integral]
    exact hintegral
  by_contra htop
  let P : Submodule ℂ (FiniteMellinNode nodes → ℂ) :=
    Submodule.span ℂ
      (Set.range (windowedFiniteMellinVector nodes a b))
  have hproper : P < ⊤ := (show P ≠ ⊤ from htop).lt_top
  rcases Submodule.exists_le_ker_of_lt_top P hproper with
    ⟨L, hL_ne, hP_le_ker⟩
  rcases hsep L hL_ne with ⟨p, hp⟩
  have hp_mem : windowedFiniteMellinVector nodes a b p ∈ P :=
    Submodule.subset_span (Set.mem_range_self p)
  exact hp (hP_le_ker hp_mem)

/-- Every assignment on a finite set of distinct complex nodes is realized by
one compact test supported inside any fixed positive window containing `1`. -/
theorem fixed_window_finite_mellin_surjective
    (nodes : Finset ℂ) {a b : ℝ}
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    ∀ y : FiniteMellinNode nodes → ℂ,
      ∃ g,
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
            (fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Ioo a b ∧
        ∀ z : FiniteMellinNode nodes,
          normalizedCC20TestSpace.mellinAt g z.1 = y z := by
  intro y
  have hspan :=
    windowedFiniteMellinVector_span_top nodes ha ha_one hone_b
  have hy_mem : y ∈ Submodule.span ℂ
      (Set.range (windowedFiniteMellinVector nodes a b)) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hy_mem with
    ⟨c, hc⟩
  let g : normalizedCC20ConcreteTestAlgebra.Test :=
    windowedPositiveIntervalCompactTestCombination c
  refine ⟨g,
    windowedPositiveIntervalCompactTestCombination_compactSupportSmooth c,
    windowedPositiveIntervalCompactTestCombination_support_subset c, ?_⟩
  intro z
  rw [windowedFiniteMellinVector_combination]
  have hpoint := congr_fun hc z
  simpa [Finsupp.sum, Pi.smul_apply, smul_eq_mul] using hpoint

/-- The nearby source zeros can be interpolated together with any additional
finite route nodes in the same fixed support window. -/
theorem fixed_window_nearby_zero_mellin_surjective
    (rho : ℂ) (R : ℝ) (routeNodes : Finset ℂ)
    {a b : ℝ} (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    ∀ y : FiniteMellinNode
        (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes) → ℂ,
      ∃ g,
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
            (fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Ioo a b ∧
        ∀ z : FiniteMellinNode
            (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
          normalizedCC20TestSpace.mellinAt g z.1 = y z :=
  fixed_window_finite_mellin_surjective
    (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes)
    ha ha_one hone_b

end CC20YoshidaNearZeros
end Source
end ConnesWeilRH
