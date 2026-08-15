# -*- coding: utf-8 -*-
# Append the H-A1 main theorem + analytic-on-ball deliverable.
from pathlib import Path

path = Path(__file__).resolve().parents[1] / "ConnesWeilRH" / "Dev" / \
    "C1XiGlobalWeightedZeroSum.lean"
with path.open("r", encoding="utf-8") as f:
    src = f.read()

anchor = "  rw [tsum_eq_sum_range (f := L) N]\n  dsimp [L]\n  rfl\n"
assert src.count(anchor) == 1, "anchor not found"

body = r'''  rw [tsum_eq_sum_range (f := L) N]
  dsimp [L]
  rfl

/-- H-A1: off the zero set, the weighted zero sum is holomorphic.  The
statement is existential in the derivative value: the analyticity consumers
(H-A2/H-A4) need only the fact, while the explicit derivative form
`weightedRegularizedZeroDeriv` is recovered by the split identity above when
the canonical identity is assembled.  Proof: on a small ball around `z0` that
avoids the zero set and stays in one dyadic strip, every shell summand is
holomorphic (`weightedRegularizedZeroTerm_hasDerivAt`), the shell derivative
bounds are uniform (`weightedRegularizedZeroDeriv_norm_le` + geometric mass),
so `hasDerivAt_tsum_of_isPreconnected` applies to the shifted shells; the
finite prefix is a finite sum of the same summands; the two assembly pieces
match `weightedRegularizedZeroSum` on the ball by
`weightedRegularizedZeroSum_split_shell`. -/
theorem weightedRegularizedZeroSum_hasDerivAt (z0 : Complex)
    (hz0 : completedRiemannXi z0 ≠ 0) :
    ∃ D : Complex, HasDerivAt weightedRegularizedZeroSum D z0 := by
  classical
  let n0 : Nat := dyadicShellIndex |z0.im| + 1
  have hs_lt0 : |z0.im| < (2 : Real) ^ n0 := by
    dsimp only [n0]
    exact lt_two_pow_succ_dyadicShellIndex |z0.im|
  have hclosed : IsClosed {z : Complex | completedRiemannXi z = 0} := by
    exact isClosed_eq (differentiable_completedRiemannXi.continuous)
      continuous_const
  have hdelta : ∃ eps : Real, 0 < eps ∧
      Metric.ball z0 eps ⊆ (Set.compl {z : Complex | completedRiemannXi z = 0}) := by
    have hmem : z0 ∈ (Set.compl {z : Complex | completedRiemannXi z = 0}) := by
      simpa using hz0
    exact ((Metric.isOpen_iff).mp hclosed.isOpen_compl) z0 hmem
  rcases hdelta with ⟨eps, heps, hball_eps⟩
  have hgap : 0 < (2 : Real) ^ n0 - |z0.im| := by nlinarith [hs_lt0]
  let r : Real := min eps ((2 ^ n0 - |z0.im|) / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min heps (div_pos hgap (by norm_num))
  have hball_in_eps : Metric.ball z0 r ⊆ Metric.ball z0 eps :=
    Metric.ball_subset_ball (by dsimp [r]; exact min_le_left _ _)
  let B : Real := ‖z0‖ + r
  have hy_norm (y : Complex) (hy : y ∈ Metric.ball z0 r) : ‖y‖ <= B := by
    have hyt : ‖y - z0‖ < r := by
      rw [Metric.mem_ball] at hy
      simpa [dist_eq_norm] using hy
    dsimp [B]
    calc
      ‖y‖ <= ‖y - z0‖ + ‖z0‖ := by
            have hw : ‖(y - z0) + z0‖ <= ‖y - z0‖ + ‖z0‖ :=
              norm_add_le (y - z0) z0
            simpa [sub_add_cancel] using hw
      _ <= r + ‖z0‖ := by nlinarith [hyt.le]
  have hy_im (y : Complex) (hy : y ∈ Metric.ball z0 r) : |y.im| < (2 : Real) ^ n0 := by
    have hyt : ‖y - z0‖ < r := by
      rw [Metric.mem_ball] at hy
      simpa [dist_eq_norm] using hy
    have hre : |y.im - z0.im| <= ‖y - z0‖ := by
      simpa using (Complex.abs_im_le_norm (y - z0))
    have htri : |y.im| <= |z0.im| + r := by
      calc
        |y.im| = |z0.im + (y.im - z0.im)| := by
              congr 1
              ring
        _ <= |z0.im| + |y.im - z0.im| := abs_add _ _
        _ <= |z0.im| + r := by nlinarith [hre, hyt.le]
    have hhalf : r <= (2 ^ n0 - |z0.im|) / 2 := by
      dsimp [r]
      exact min_le_right _ _
    nlinarith [hs_lt0, hhalf]
  have hy_xi (y : Complex) (hy : y ∈ Metric.ball z0 r) :
      completedRiemannXi y ≠ 0 := by
    have hyc : y ∉ {z : Complex | completedRiemannXi z = 0} :=
      hball_eps (hball_in_eps hy)
    simpa using hyc
  have hne_per (y : Complex) (hy : y ∈ Metric.ball z0 r)
      (rho : sourceNontrivialZeroSet) : y - rho.1 ≠ 0 := by
    intro heq
    apply hy_xi y hy
    have hzero_rho : completedRiemannXi rho.1 = 0 :=
      completedRiemannXi_eq_zero_of_mem_sourceNontrivialZeroSet
    simpa [heq] using hzero_rho
  let g : Nat -> Complex -> Complex := fun m z =>
    ∑' rho : spectralHeightShell (m + n0 + 1),
      weightedRegularizedZeroTerm z rho.1
  let g' : Nat -> Complex -> Complex := fun m z =>
    ∑' rho : spectralHeightShell (m + n0 + 1),
      weightedRegularizedZeroDeriv z rho.1
  let u : Nat -> Real := fun m =>
    spectralMultiplicityConstant * (3 / 4 : Real) ^ (m + n0)
  have hu : Summable u := by
    have hgeo : Summable (fun m : Nat => (3 / 4 : Real) ^ (m + n0)) := by
      simpa [pow_add, mul_assoc] using
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
          ((3 / 4 : Real) ^ n0)
    simpa [u, mul_assoc, mul_left_comm, mul_comm] using
      hgeo.mul_left spectralMultiplicityConstant
  have hmassN (k : Nat) :
      (∑ rho : spectralHeightShell (k + 1), (xiMultiplicity rho.1 : Real)) <=
        spectralMultiplicityConstant * 3 ^ k := by
    simpa [spectralHeightMultiplicity] using
      spectralHeightMultiplicity_geometric_bound k
  have hg : ∀ m y, y ∈ Metric.ball z0 r → HasDerivAt (g m) (g' m y) y := by
    intro m y hy
    dsimp [g, g']
    letI := (spectralHeightShell_finite (m + n0 + 1)).fintype
    rw [tsum_fintype]
    refine (Finset.sum_hasDerivAt ?_)
    intro rho hrho
    exact weightedRegularizedZeroTerm_hasDerivAt (hne_per y hy rho)
  have hg' : ∀ m y, y ∈ Metric.ball z0 r → ‖g' m y‖ <= u m := by
    intro m y hy
    dsimp [g', u]
    letI := (spectralHeightShell_finite (m + n0 + 1)).fintype
    have hbound : (∑ rho : spectralHeightShell (m + n0 + 1),
        ‖weightedRegularizedZeroDeriv y rho.1‖) <=
        (∑ rho : spectralHeightShell (m + n0 + 1),
          (xiMultiplicity rho.1 : Real)) / ((2 : Real) ^ (m + n0)) ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun rho hrho =>
        weightedRegularizedZeroDeriv_norm_le y (m + n0) n0
          (by omega) (hy_im y hy) rho.2
    calc
      ‖∑' rho : spectralHeightShell (m + n0 + 1),
          weightedRegularizedZeroDeriv y rho.1‖ <=
        (∑ rho : spectralHeightShell (m + n0 + 1),
            ‖weightedRegularizedZeroDeriv y rho.1‖) := by
              rw [tsum_fintype]
              exact norm_sum_le _ _
      _ <= (∑ rho : spectralHeightShell (m + n0 + 1),
            (xiMultiplicity rho.1 : Real)) / ((2 : Real) ^ (m + n0)) ^ 2 := hbound
      _ <= spectralMultiplicityConstant * (3 / 4 : Real) ^ (m + n0) := by
            have hpow : (spectralMultiplicityConstant * 3 ^ (m + n0)) /
                ((2 : Real) ^ (m + n0)) ^ 2 =
                spectralMultiplicityConstant * (3 / 4 : Real) ^ (m + n0) := by
              rw [pow_two]
              have hfour : (2 : Real) ^ (m + n0) * (2 : Real) ^ (m + n0) =
                  4 ^ (m + n0) := by
                rw [← mul_pow]
                norm_num
              rw [hfour, div_pow]
              ring
            rw [hpow]
            exact div_le_div_of_nonneg_right (hmassN (m + n0))
              (sq_pos_of_pos (pow_pos (by norm_num : (0 : Real) < 2) (m + n0)))
  have hg0 : Summable fun m => g m z0 := by
    refine Summable.of_norm_bounded
      (fun m => spectralMultiplicityConstant * (2 * B) *
        (3 / 4 : Real) ^ (m + n0)) ?_ ?_
    · have hgeo : Summable (fun m : Nat => (3 / 4 : Real) ^ (m + n0)) := by
        simpa [pow_add, mul_assoc] using
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
            ((3 / 4 : Real) ^ n0)
      simpa [mul_assoc] using hgeo.mul_left (spectralMultiplicityConstant * (2 * B))
    · intro m
      dsimp [g]
      letI := (spectralHeightShell_finite (m + n0 + 1)).fintype
      calc
        ‖∑' rho : spectralHeightShell (m + n0 + 1),
            weightedRegularizedZeroTerm z0 rho.1‖ <=
          ∑ rho : spectralHeightShell (m + n0 + 1),
            ‖weightedRegularizedZeroTerm z0 rho.1‖ := by
              rw [tsum_fintype]
              exact norm_sum_le _ _
        _ <= ∑ rho : spectralHeightShell (m + n0 + 1),
              (xiMultiplicity rho.1 : Real) *
                (2 * ‖z0‖ / ((2 : Real) ^ (m + n0)) ^ 2) := by
              exact Finset.sum_le_sum fun rho hrho =>
                weightedRegularizedZeroTerm_norm_le z0 (m + n0) n0 (by omega)
                  hs_lt0 rho.2
        _ = (∑ rho : spectralHeightShell (m + n0 + 1),
              (xiMultiplicity rho.1 : Real)) *
              (2 * ‖z0‖ / ((2 : Real) ^ (m + n0)) ^ 2) := by
              rw [Finset.sum_mul]
        _ <= (spectralMultiplicityConstant * 3 ^ (m + n0)) *
              (2 * ‖z0‖ / ((2 : Real) ^ (m + n0)) ^ 2) := by
              exact mul_le_mul_of_nonneg_right (hmassN (m + n0))
                (div_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2)
                  (norm_nonneg z0)) (sq_nonneg _))
        _ = spectralMultiplicityConstant * (2 * ‖z0‖) *
              (3 / 4 : Real) ^ (m + n0) := by
              rw [pow_two]
              have hfour : (2 : Real) ^ (m + n0) * (2 : Real) ^ (m + n0) =
                  4 ^ (m + n0) := by
                rw [← mul_pow]
                norm_num
              rw [hfour, div_pow]
              ring
        _ <= spectralMultiplicityConstant * (2 * B) *
              (3 / 4 : Real) ^ (m + n0) := by
              gcongr
              dsimp [B]
              nlinarith [hr.le, norm_nonneg z0]
  have hpre : HasDerivAt (fun z : Complex =>
        ∑ m in Finset.range n0, ∑' rho : spectralHeightShell (m + 1),
          weightedRegularizedZeroTerm z rho.1)
      (∑ m in Finset.range n0, ∑' rho : spectralHeightShell (m + 1),
        weightedRegularizedZeroDeriv z0 rho.1) z0 := by
    refine (Finset.sum_hasDerivAt ?_)
    intro m hm
    letI := (spectralHeightShell_finite (m + 1)).fintype
    rw [tsum_fintype]
    refine (Finset.sum_hasDerivAt ?_)
    intro rho hrho
    exact weightedRegularizedZeroTerm_hasDerivAt (hne_per z0 (mem_ball_self hr) rho)
  have hth : HasDerivAt (fun z : Complex => ∑' m : Nat, g m z)
      (∑' m : Nat, g' m z0) z0 := by
    exact hasDerivAt_tsum_of_isPreconnected hu (Metric.isOpen_ball)
      (Metric.isPreconnected_ball) hg hg' (mem_ball_self hr) hg0 (mem_ball_self hr)
  have hmain : HasDerivAt (fun z : Complex =>
        (∑ m in Finset.range n0, ∑' rho : spectralHeightShell (m + 1),
          weightedRegularizedZeroTerm z rho.1) + (∑' m : Nat, g m z))
      ((∑ m in Finset.range n0, ∑' rho : spectralHeightShell (m + 1),
          weightedRegularizedZeroDeriv z0 rho.1) + (∑' m : Nat, g' m z0)) z0 :=
    hpre.add hth
  refine ⟨(∑ m in Finset.range n0, ∑' rho : spectralHeightShell (m + 1),
        weightedRegularizedZeroDeriv z0 rho.1) + (∑' m : Nat, g' m z0), ?_⟩
  have hF_eq : (fun z : Complex => weightedRegularizedZeroSum z) =ᶠ[𝓝 z0]
      (fun z : Complex =>
        (∑ m in Finset.range n0, ∑' rho : spectralHeightShell (m + 1),
          weightedRegularizedZeroTerm z rho.1) + (∑' m : Nat, g m z)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    dsimp [g]
    rw [← weightedRegularizedZeroSum_split_shell z n0]
  exact hmain.congr_of_eventuallyEq hF_eq (by rfl)

/-- H-A1 deliverable: analyticity on an open ball around every non-zero point
of the completed xi function. -/
theorem weightedRegularizedZeroSum_analyticOn_ball {s0 : Complex}
    (hs0 : completedRiemannXi s0 ≠ 0) :
    ∃ r > 0, AnalyticOnNhd ℂ weightedRegularizedZeroSum (Metric.ball s0 r) := by
  classical
  let n0 : Nat := dyadicShellIndex |s0.im| + 1
  have hs0_lt : |s0.im| < (2 : Real) ^ n0 := by
    dsimp only [n0]
    exact lt_two_pow_succ_dyadicShellIndex |s0.im|
  have hclosed : IsClosed {z : Complex | completedRiemannXi z = 0} := by
    exact isClosed_eq (differentiable_completedRiemannXi.continuous)
      continuous_const
  have hdelta : ∃ eps : Real, 0 < eps ∧
      Metric.ball s0 eps ⊆ (Set.compl {z : Complex | completedRiemannXi z = 0}) := by
    have hmem : s0 ∈ (Set.compl {z : Complex | completedRiemannXi z = 0}) := by
      simpa using hs0
    exact ((Metric.isOpen_iff).mp hclosed.isOpen_compl) s0 hmem
  rcases hdelta with ⟨eps, heps, hball_eps⟩
  have hgap : 0 < (2 : Real) ^ n0 - |s0.im| := by nlinarith [hs0_lt]
  let r : Real := min eps ((2 ^ n0 - |s0.im|) / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min heps (div_pos hgap (by norm_num))
  refine ⟨r, hr, ?_⟩
  intro z hz
  have hball : Metric.ball s0 r ⊆ Metric.ball s0 eps :=
    Metric.ball_subset_ball (by dsimp [r]; exact min_le_left _ _)
  have hz_xi : completedRiemannXi z ≠ 0 := by
    have hzc : z ∉ {z : Complex | completedRiemannXi z = 0} :=
      hball_eps (hball hz)
    simpa using hzc
  rcases (weightedRegularizedZeroSum_hasDerivAt z hz_xi) with ⟨Dz, hDz⟩
  exact hDz.differentiableAt.analyticAt

'''

out = src.replace(anchor, body, 1)
with path.open("w", encoding="utf-8") as f:
    f.write(out)
print("OK appended main theorem, new length:", len(out))
