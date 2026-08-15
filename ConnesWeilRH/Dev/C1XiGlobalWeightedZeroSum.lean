import ConnesWeilRH.Dev.C1XiGlobalZeroSum
import ConnesWeilRH.Dev.C1SpectralSummability
import ConnesWeilRH.Dev.C1SpectralWeil
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# C1XiGlobalWeightedZeroSum - multiplicity-weighted zero sum (H-A0)

The (H) brick targets the canonical regularized log-derivative identity

```text
xi'/xi(s) = b + sum over ALL nontrivial zeros rho of
              m_rho * ( 1/(s-rho) + 1/rho )            (m_rho = xiMultiplicity rho)
```

The unweighted summation machinery lives in `C1XiGlobalZeroSum` (brick G);
this module supplies the *weighted* summability step (H-A0), the only input
the identity needs that was not already unconditional:

- `weightedRegularizedZeroTerm`: the summand `m_rho * (1/(s-rho) + 1/rho)`;
- `weightedRegularizedZeroTerm_norm_le`: the pointwise shell bound, which is
  exactly the unweighted bound times `m_rho` (the multiplicity comes out of
  the norm as a plain nonnegative scalar — no quadratic multiplicity appears);
- `weightedRegularizedZeroSummable`: unconditional summability of the
  weighted sum over the whole zero set, from the closed shell-mass bound
  `mass (n+1) <= K * 3^n` against the denominator `4^n` — the brick-G
  argument verbatim, so no subexponential multiplicity bound is needed.

The value bound for consumers is still brick G's unweighted
`regularizedZeroTail_norm_shellSum_le`, inflated by `1 <= xiMultiplicity rho`
at assembly time (design 1013, D1 + D4).
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiGlobalWeightedZeroSum

open scoped BigOperators
open C1XiGlobalZeroSum
open C1SpectralWeil
open C1SpectralSummability
open CC20YoshidaNearZeros
open CC20ZetaCounting

noncomputable section

/-- One multiplicity-weighted summand of the canonical regularized zero sum:
`m_rho * (1/(s-rho) + 1/rho)`.  This is the pole coefficient matched by
`logDeriv xi` at a zero of order `m_rho`; the unweighted brick-G terms are
used only as bounds, with `1 <= m_rho` inflating. -/
noncomputable def weightedRegularizedZeroTerm (s : Complex)
    (rho : sourceNontrivialZeroSet) : Complex :=
  algebraMap ℝ ℂ (xiMultiplicity rho : Real) * regularizedZeroTerm s rho

/-- Pointwise norm bound inside shell `n + 1`: the multiplicity factor
factors out of the norm as a nonnegative scalar, so
`||weighted term|| <= m_rho * (2*||s|| / (2^n)^2)` — the unweighted shell
bound times exactly `m_rho`. -/
theorem weightedRegularizedZeroTerm_norm_le (s : Complex)
    (n n0 : Nat) (hn : n0 <= n) (hs_lt : |s.im| < (2 : Real) ^ n0)
    {rho : sourceNontrivialZeroSet}
    (hrho : rho ∈ spectralHeightShell (n + 1)) :
    ‖weightedRegularizedZeroTerm s rho‖ <=
      (xiMultiplicity rho : Real) *
        (2 * ‖s‖ / ((2 : Real) ^ n) ^ 2) := by
  unfold weightedRegularizedZeroTerm
  have hcast : ‖algebraMap ℝ ℂ (xiMultiplicity rho : Real)‖ =
      (xiMultiplicity rho : Real) := by
    rw [norm_algebraMap]
    rw [Real.norm_eq_abs]
    rw [norm_one, mul_one]
    rw [abs_of_nonneg]
    exact_mod_cast (Nat.zero_le (xiMultiplicity rho))
  have hmultNonneg : 0 <= (xiMultiplicity rho : Real) := by
    exact_mod_cast (Nat.zero_le (xiMultiplicity rho))
  calc
    ‖algebraMap ℝ ℂ (xiMultiplicity rho : Real) * regularizedZeroTerm s rho‖ =
        ‖algebraMap ℝ ℂ (xiMultiplicity rho : Real)‖ *
          ‖regularizedZeroTerm s rho‖ := by
          rw [norm_mul]
    _ = (xiMultiplicity rho : Real) * ‖regularizedZeroTerm s rho‖ := by
          rw [hcast]
    _ <= (xiMultiplicity rho : Real) *
          (2 * ‖s‖ / ((2 : Real) ^ n) ^ 2) := by
          exact mul_le_mul_of_nonneg_left
            (regularizedZeroTerm_norm_shell_le s n n0 hn hs_lt hrho)
            hmultNonneg

/-- The multiplicity-weighted regularized zero sum is unconditionally
summable at every point and for every dyadic height bound on `|Im s|` — the
brick-G shell-mass argument verbatim, with the weight being the multiplicity
itself. -/
theorem weightedRegularizedZeroSummable (s : Complex) :
    Summable (fun rho : sourceNontrivialZeroSet =>
      weightedRegularizedZeroTerm s rho) := by
  apply Summable.of_norm
  let n0 : Nat := dyadicShellIndex |s.im| + 1
  have hs_lt : |s.im| < (2 : Real) ^ n0 := by
    dsimp only [n0]
    exact lt_two_pow_succ_dyadicShellIndex |s.im|
  exact summable_of_shell_weight_tail_bound
    (f := fun rho => ‖weightedRegularizedZeroTerm s rho‖)
    (weight := fun rho => (xiMultiplicity rho : Real))
    (shell := spectralHeightShell)
    (hf := fun rho => norm_nonneg _)
    (hpartition := spectralHeightShell_partition)
    (hfinite := spectralHeightShell_finite)
    (K := spectralMultiplicityConstant) (B := 2 * ‖s‖) (q := 3)
    (n0 := n0)
    (hB := mul_nonneg (by norm_num : (0 : Real) <= 2) (norm_nonneg s))
    (hq := by norm_num) (hq4 := by norm_num)
    (hmass := fun n => by
      simpa [spectralHeightMultiplicity] using
        spectralHeightMultiplicity_geometric_bound n)
    (hpoint := fun n hn x =>
      weightedRegularizedZeroTerm_norm_le s n n0 hn hs_lt x.2)

/-! ### H-A1: analyticity of the weighted zero sum off the zero set

The (H) brick also needs the *function theory* of the weighted sum, not just
its summability: on a neighborhood of any point away from the zeros of
`completedRiemannXi`, the sum is holomorphic, with derivative the shell-ordered
weighted derivative sum.  This is the input of the removable-pole step (H-A2).

The summation is indexed in *shell order* (the sum over `m` of the finite
shell `m`); this includes the zeroth shell, so it is an honest reindexing of
the whole source zero set.  The shell order is the one that carries a
*uniform* derivative bound on the tail: on shell `n + 1` the denominator separation
`|Im s - Im rho| >= 2^n` is uniform in `s` as long as `s` stays in a fixed
horizontal strip. -/

/-- The weighted zero sum in shell-ordered form.  Each inner sum is finite
(one dyadic shell), including shell `0`. -/
noncomputable def weightedRegularizedZeroSum (s : Complex) : Complex :=
  ∑' m : Nat, ∑' rho : spectralHeightShell m,
    weightedRegularizedZeroTerm s rho.1

/-! The shell order is an unconditional tsum, so it can be reindexed through
the partition equivalence without changing the value.  H-A2 needs this
source-indexed readback in order to remove one selected zero with the standard
subtype-complement sum theorem. -/

/-- The shell-ordered weighted sum is the same unconditional sum over the
source zero subtype.  The equivalence is the exact `spectralHeightShell`
partition owner; no arbitrary enumeration of zeros is introduced. -/
theorem weightedRegularizedZeroSum_eq_source_tsum (s : Complex) :
    weightedRegularizedZeroSum s =
      ∑' rho : sourceNontrivialZeroSet,
        weightedRegularizedZeroTerm s rho := by
  let e := Set.sigmaEquiv spectralHeightShell spectralHeightShell_partition
  have hsource : Summable (fun rho : sourceNontrivialZeroSet =>
      weightedRegularizedZeroTerm s rho) :=
    weightedRegularizedZeroSummable s
  have hsigma : Summable (fun p : Σ m, spectralHeightShell m =>
      weightedRegularizedZeroTerm s p.2.1) := by
    simpa only [e, Function.comp_apply] using
      (e.summable_iff.mpr hsource)
  calc
    weightedRegularizedZeroSum s =
        ∑' m : Nat, ∑' rho : spectralHeightShell m,
          weightedRegularizedZeroTerm s rho.1 := rfl
    _ = ∑' p : Σ m, spectralHeightShell m,
          weightedRegularizedZeroTerm s p.2.1 := by
      symm
      simpa only using hsigma.tsum_sigma
    _ = ∑' rho : sourceNontrivialZeroSet,
          weightedRegularizedZeroTerm s rho := by
      simpa only [e, Set.sigmaEquiv, Function.comp_apply] using
        e.tsum_eq (fun rho : sourceNontrivialZeroSet =>
          weightedRegularizedZeroTerm s rho)

/-- The shell layer itself is summable.  This is the reusable convergence
fact for finite-prefix/shifted-tail decompositions at a selected zero. -/
theorem weightedRegularizedZeroShellSummable (s : Complex) :
    Summable (fun m : Nat =>
      ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm s rho.1) := by
  have hnorm : Summable (fun rho : sourceNontrivialZeroSet =>
      ‖weightedRegularizedZeroTerm s rho‖) :=
    (weightedRegularizedZeroSummable s).norm
  have hpart := (summable_partition
    (f := fun rho : sourceNontrivialZeroSet =>
      ‖weightedRegularizedZeroTerm s rho‖)
    (hf := fun rho => norm_nonneg _) spectralHeightShell_partition).mp hnorm
  have hnormLayers : Summable (fun m : Nat =>
      ∑' rho : spectralHeightShell m,
        ‖weightedRegularizedZeroTerm s rho.1‖) := by
    simpa using hpart.2
  refine Summable.of_norm_bounded hnormLayers ?_
  intro m
  letI := (spectralHeightShell_finite m).fintype
  calc
    ‖∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm s rho.1‖ =
        ‖∑ rho : spectralHeightShell m,
          weightedRegularizedZeroTerm s rho.1‖ := by
            rw [tsum_fintype]
    _ <= ∑ rho : spectralHeightShell m,
          ‖weightedRegularizedZeroTerm s rho.1‖ := by
            exact norm_sum_le _ _
    _ = ∑' rho : spectralHeightShell m,
          ‖weightedRegularizedZeroTerm s rho.1‖ := by
            rw [tsum_fintype]

/-- Derivative atom: `d/ds [ m_rho * (1/(s-rho) + 1/rho) ] = -m_rho / (s-rho)^2`,
with the constant `1/rho` term differentiated away. -/
noncomputable def weightedRegularizedZeroDeriv (s : Complex)
    (rho : sourceNontrivialZeroSet) : Complex :=
  -algebraMap ℝ ℂ (xiMultiplicity rho : Real) * (s - rho.1)⁻¹ ^ 2

/-- Off the diagonal `s = rho`, the weighted summand is holomorphic with the
displayed derivative. -/
theorem weightedRegularizedZeroTerm_hasDerivAt {s0 : Complex}
    {rho : sourceNontrivialZeroSet} (hsr : s0 - rho.1 ≠ 0) :
    HasDerivAt (fun s : Complex => weightedRegularizedZeroTerm s rho)
      (weightedRegularizedZeroDeriv s0 rho) s0 := by
  unfold weightedRegularizedZeroTerm weightedRegularizedZeroDeriv
  have hinv : HasDerivAt (fun s : Complex => (s - rho.1)⁻¹)
      (-(s0 - rho.1)⁻¹ ^ 2) s0 := by
    have hsub : HasDerivAt (fun s : Complex => s - rho.1) 1 s0 := by
      simpa using (hasDerivAt_id' (x := s0)).sub_const (rho.1 : Complex)
    convert hsub.inv hsr using 1
    field_simp [pow_two]
  have hconst : HasDerivAt (fun s : Complex => (1 : ℂ) / rho.1) 0 s0 :=
    hasDerivAt_const (x := s0) (c := (1 : ℂ) / rho.1)
  have hmain : HasDerivAt (fun s : Complex => (s - rho.1)⁻¹ + (1 : ℂ) / rho.1)
      (-(s0 - rho.1)⁻¹ ^ 2) s0 := by
    convert hinv.add hconst using 1 <;> simp
  have hreg : HasDerivAt (fun s : Complex => regularizedZeroTerm s rho)
      (-(s0 - rho.1)⁻¹ ^ 2) s0 := by
    simpa [regularizedZeroTerm, div_eq_mul_inv] using hmain
  have hmul := hreg.const_mul (algebraMap ℝ ℂ (xiMultiplicity rho : Real))
  simpa [mul_assoc, mul_comm, mul_left_comm, neg_mul, mul_neg] using hmul

/-- Pointwise norm bound for the derivative atom inside shell `n + 1`: the
denominator separation `|Im s - Im rho| >= 2^n` gives
`||-m_rho/(s-rho)^2|| <= m_rho / (2^n)^2`. -/
theorem weightedRegularizedZeroDeriv_norm_le (s : Complex) (n n0 : Nat)
    (hn : n0 <= n) (hs_lt : |s.im| < (2 : Real) ^ n0)
    {rho : sourceNontrivialZeroSet} (hrho : rho ∈ spectralHeightShell (n + 1)) :
    ‖weightedRegularizedZeroDeriv s rho‖ <=
      (xiMultiplicity rho : Real) / ((2 : Real) ^ n) ^ 2 := by
  have him : (2 : Real) ^ (n + 1) <= |rho.1.im| := shell_lower_im hrho
  have hrho_nonzero : rho.1 ≠ 0 := by
    intro hz
    have him0 : |rho.1.im| = 0 := by simp [hz]
    nlinarith [him, him0,
      pow_pos (by norm_num : (0 : Real) < 2) (n + 1)]
  have hdist_abs : |rho.1.im| - |s.im| <= |rho.1.im - s.im| :=
    abs_sub_abs_le_abs_sub rho.1.im s.im
  have hsm : |s.im| <= (2 : Real) ^ n0 := hs_lt.le
  have hpowUp : (2 : Real) ^ n0 <= (2 : Real) ^ n :=
    pow_le_pow_right₀ (by norm_num : (1 : Real) <= 2) hn
  have hpowThrough : (2 : Real) ^ (n + 1) - (2 : Real) ^ n0 >=
      (2 : Real) ^ n := by
    rw [pow_succ]
    nlinarith [hpowUp,
      pow_nonneg (by norm_num : (0 : Real) <= 2) n]
  have hseparationIm : (2 : Real) ^ n <= |rho.1.im - s.im| := by
    nlinarith [him, hsm, hpowThrough, hdist_abs,
      pow_nonneg (by norm_num : (0 : Real) <= 2) n]
  have hsp : (2 : Real) ^ n <= ‖s - rho.1‖ := by
    calc
      (2 : Real) ^ n <= |rho.1.im - s.im| := hseparationIm
      _ = |(s - rho.1).im| := by
        simpa using (abs_sub_comm rho.1.im s.im)
      _ <= ‖s - rho.1‖ := Complex.abs_im_le_norm (s - rho.1)
  have hne : s - rho.1 ≠ 0 := by
    intro hz
    have : ‖s - rho.1‖ = 0 := by simp [hz]
    nlinarith [hsp, this,
      pow_pos (by norm_num : (0 : Real) < 2) n]
  calc
    ‖weightedRegularizedZeroDeriv s rho‖ =
        (xiMultiplicity rho : Real) * ‖(s - rho.1)⁻¹‖ ^ 2 := by
          simp [weightedRegularizedZeroDeriv, norm_mul, norm_neg, norm_algebraMap,
            Real.norm_eq_abs, abs_of_nonneg, norm_inv, pow_two]
    _ = (xiMultiplicity rho : Real) / ‖s - rho.1‖ ^ 2 := by
          rw [norm_inv]
          field_simp [norm_algebraMap, Real.norm_eq_abs, abs_of_nonneg,
            pow_two, norm_ne_zero_iff.mpr hne]
    _ <= (xiMultiplicity rho : Real) / ((2 : Real) ^ n) ^ 2 := by
          have hsq : ((2 : Real) ^ n) ^ 2 <= ‖s - rho.1‖ ^ 2 := by
            have hnonneg : 0 <= (2 : Real) ^ n := pow_nonneg (by norm_num) n
            exact (sq_le_sq.mpr (by simpa [abs_of_nonneg hnonneg] using hsp))
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
            (sq_pos_of_pos (pow_pos (by norm_num : (0 : Real) < 2) n)) hsq

/-- Every element of the source nontrivial zero set is a zero of the completed
xi function: the zero-set identification of `CC20ZetaCounting`. -/
lemma completedRiemannXi_eq_zero_of_mem_sourceNontrivialZeroSet
    {rho : sourceNontrivialZeroSet} : completedRiemannXi rho.1 = 0 :=
  (completedRiemannXi_eq_zero_iff_sourceNontrivialZero rho.1).mpr rho.2

/-- The shell-ordered sum splits at a dyadic height `N`: the prefix shells
`0 .. N - 1` plus the shifted tail from `N` upward.  Unconditional because
each inner shell sum is finite and the tail is dominated by the geometric
mass bound (brick G), which makes the whole layer sequence summable. -/
theorem weightedRegularizedZeroSum_split_shell (s : Complex) (N : Nat) :
    (∑' m : Nat, ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm s rho.1) =
      (∑ m ∈ Finset.range N, ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm s rho.1) +
      (∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        weightedRegularizedZeroTerm s rho.1) := by
  let L : Nat -> Complex := fun m =>
    ∑' rho : spectralHeightShell m, weightedRegularizedZeroTerm s rho.1
  have hL_summable : Summable L := by
    -- 层内有限 → 层和的可加性从 H-A0 的 rho-序可加性 + partition 分解直接来，
    -- 不需要逐层分离界：每层和 bounded by (∑' x, ‖wTerm s x‖) 的层切片
    have hnorm : Summable (fun rho : sourceNontrivialZeroSet =>
        ‖weightedRegularizedZeroTerm s rho‖) :=
      (weightedRegularizedZeroSummable s).norm
    have hpart := (summable_partition
      (f := fun rho : sourceNontrivialZeroSet => ‖weightedRegularizedZeroTerm s rho‖)
      (hf := fun rho => norm_nonneg _) spectralHeightShell_partition).mp hnorm
    have hnormLayers : Summable (fun m : Nat =>
        ∑' rho : spectralHeightShell m, ‖weightedRegularizedZeroTerm s rho.1‖) := by
      simpa using hpart.2
    refine Summable.of_norm_bounded hnormLayers ?_
    intro m
    letI := (spectralHeightShell_finite m).fintype
    calc
      ‖∑' rho : spectralHeightShell m,
          weightedRegularizedZeroTerm s rho.1‖ =
          ‖∑ rho : spectralHeightShell m,
            weightedRegularizedZeroTerm s rho.1‖ := by
              rw [tsum_fintype]
      _ <= ∑ rho : spectralHeightShell m,
            ‖weightedRegularizedZeroTerm s rho.1‖ := by
              exact norm_sum_le _ _
      _ = ∑' rho : spectralHeightShell m,
            ‖weightedRegularizedZeroTerm s rho.1‖ := by
              rw [tsum_fintype]
  simpa [L] using (hL_summable.sum_add_tsum_nat_add N).symm

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
    _ <= ‖z0‖ + r := by nlinarith [hyt.le]
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
        _ <= |z0.im| + |y.im - z0.im| := abs_add_le _ _
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
    have hy_eq : y = rho.1 := sub_eq_zero.mp heq
    rw [hy_eq]
    exact hzero_rho
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
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using
        (summable_geometric_of_lt_one (r := (3 / 4 : Real)) (by norm_num) (by norm_num)).mul_left
          ((3 / 4 : Real) ^ n0)
    simpa [u, mul_assoc, mul_left_comm, mul_comm] using
      hgeo.mul_left spectralMultiplicityConstant
  have hmassN (k : Nat) :
      (∑' rho : spectralHeightShell (k + 1), (xiMultiplicity rho.1 : Real)) <=
        spectralMultiplicityConstant * 3 ^ k := by
    simpa [spectralHeightMultiplicity] using
      spectralHeightMultiplicity_geometric_bound k
  have hg : ∀ m y, y ∈ Metric.ball z0 r → HasDerivAt (g m) (g' m y) y := by
    intro m y hy
    dsimp [g, g']
    letI := (spectralHeightShell_finite (m + n0 + 1)).fintype
    have hsum : HasDerivAt (fun z : Complex =>
        ∑ rho : spectralHeightShell (m + n0 + 1),
          weightedRegularizedZeroTerm z rho.1)
        (∑ rho : spectralHeightShell (m + n0 + 1),
          weightedRegularizedZeroDeriv y rho.1) y := by
      refine HasDerivAt.fun_sum ?_
      intro rho hrho
      exact weightedRegularizedZeroTerm_hasDerivAt (hne_per y hy rho)
    simpa only [tsum_fintype] using hsum
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
            have hmassN_current :
                (∑ rho : spectralHeightShell (m + n0 + 1),
                  (xiMultiplicity rho.1 : Real)) <=
                spectralMultiplicityConstant * 3 ^ (m + n0) := by
              simpa only [tsum_fintype] using hmassN (m + n0)
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
            calc
              (∑ rho : spectralHeightShell (m + n0 + 1),
                  (xiMultiplicity rho.1 : Real)) /
                  ((2 : Real) ^ (m + n0)) ^ 2 <=
                  (spectralMultiplicityConstant * 3 ^ (m + n0)) /
                    ((2 : Real) ^ (m + n0)) ^ 2 :=
                div_le_div_of_nonneg_right hmassN_current
                  (sq_nonneg _)
              _ = spectralMultiplicityConstant * (3 / 4 : Real) ^ (m + n0) := hpow
  have hg0 : Summable fun m => g m z0 := by
    have hmajor : Summable (fun m => spectralMultiplicityConstant * (2 * B) *
        (3 / 4 : Real) ^ (m + n0)) := by
      have hgeo : Summable (fun m : Nat => (3 / 4 : Real) ^ (m + n0)) := by
        simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using
          (summable_geometric_of_lt_one (r := (3 / 4 : Real)) (by norm_num) (by norm_num)).mul_left
            ((3 / 4 : Real) ^ n0)
      simpa [mul_assoc] using hgeo.mul_left (spectralMultiplicityConstant * (2 * B))
    refine hmajor.of_norm_bounded ?_
    intro m
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
              have hmassN_current :
                  (∑ rho : spectralHeightShell (m + n0 + 1),
                    (xiMultiplicity rho.1 : Real)) <=
                  spectralMultiplicityConstant * 3 ^ (m + n0) := by
                simpa only [tsum_fintype] using hmassN (m + n0)
              exact mul_le_mul_of_nonneg_right hmassN_current
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
              have hK := spectralMultiplicityConstant_nonneg
              gcongr
              dsimp [B]
              nlinarith [hr.le, norm_nonneg z0, hK]
  have hpre : HasDerivAt (fun z : Complex =>
        ∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
          weightedRegularizedZeroTerm z rho.1)
      (∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroDeriv z0 rho.1) z0 := by
    refine HasDerivAt.fun_sum (u := Finset.range (n0 + 1))
      (A := fun (m : Nat) (z : Complex) => ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm z rho.1)
      (A' := fun m => ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroDeriv z0 rho.1) ?_
    intro m hm
    letI := (spectralHeightShell_finite m).fintype
    have hsum : HasDerivAt (fun z : Complex =>
        ∑ rho : spectralHeightShell m,
          weightedRegularizedZeroTerm z rho.1)
        (∑ rho : spectralHeightShell m,
          weightedRegularizedZeroDeriv z0 rho.1) z0 := by
      refine HasDerivAt.fun_sum ?_
      intro rho hrho
      exact weightedRegularizedZeroTerm_hasDerivAt
        (hne_per z0 (Metric.mem_ball_self hr) rho)
    simpa only [tsum_fintype] using hsum
  have hth : HasDerivAt (fun z : Complex => ∑' m : Nat, g m z)
      (∑' m : Nat, g' m z0) z0 := by
    exact hasDerivAt_tsum_of_isPreconnected hu (Metric.isOpen_ball)
      (Metric.isPreconnected_ball) hg hg' (Metric.mem_ball_self hr) hg0 (Metric.mem_ball_self hr)
  have hmain : HasDerivAt (fun z : Complex =>
        (∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
          weightedRegularizedZeroTerm z rho.1) + (∑' m : Nat, g m z))
      ((∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
          weightedRegularizedZeroDeriv z0 rho.1) + (∑' m : Nat, g' m z0)) z0 :=
    hpre.add hth
  refine ⟨(∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroDeriv z0 rho.1) + (∑' m : Nat, g' m z0), ?_⟩
  have hF_eq : (fun z : Complex => weightedRegularizedZeroSum z) =ᶠ[nhds z0]
      (fun z : Complex =>
        (∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
          weightedRegularizedZeroTerm z rho.1) + (∑' m : Nat, g m z)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
    rw [weightedRegularizedZeroSum]
    rw [weightedRegularizedZeroSum_split_shell z (n0 + 1)]
    simp only [g]
    have htail :
        (∑' m : Nat, ∑' rho : spectralHeightShell (m + (n0 + 1)),
          weightedRegularizedZeroTerm z rho.1) =
        (∑' m : Nat, ∑' rho : spectralHeightShell (m + n0 + 1),
          weightedRegularizedZeroTerm z rho.1) := by
      apply tsum_congr
      intro m
      have hindex : m + (n0 + 1) = m + n0 + 1 := by omega
      rw [hindex]
    rw [htail]
  exact hmain.congr_of_eventuallyEq hF_eq

/-- H-A1 deliverable, differentiable form: the weighted zero sum is
holomorphic on an open ball around every non-zero point. -/
theorem weightedRegularizedZeroSum_differentiableOn_ball {s0 : Complex}
    (hs0 : completedRiemannXi s0 ≠ 0) :
    ∃ r > 0, DifferentiableOn ℂ weightedRegularizedZeroSum (Metric.ball s0 r) := by
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
  exact hDz.differentiableAt.differentiableWithinAt

/-- H-A1 deliverable: analyticity on an open ball around every non-zero point
of the completed xi function (Cauchy-Weierstrass via
`DifferentiableOn.analyticOnNhd`). -/
theorem weightedRegularizedZeroSum_analyticOn_ball {s0 : Complex}
    (hs0 : completedRiemannXi s0 ≠ 0) :
    ∃ r > 0, AnalyticOnNhd ℂ weightedRegularizedZeroSum (Metric.ball s0 r) := by
  rcases (weightedRegularizedZeroSum_differentiableOn_ball hs0) with ⟨r, hr, hd⟩
  exact ⟨r, hr, DifferentiableOn.analyticOnNhd hd (Metric.isOpen_ball)⟩


end

end C1XiGlobalWeightedZeroSum
end Source
end ConnesWeilRH
