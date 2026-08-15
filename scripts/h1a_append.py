# -*- coding: utf-8 -*-
# Append the H-A1 brick body to C1XiGlobalWeightedZeroSum.lean.
from pathlib import Path

path = Path(__file__).resolve().parents[1] / "ConnesWeilRH" / "Dev" / \
    "C1XiGlobalWeightedZeroSum.lean"
with path.open("r", encoding="utf-8") as f:
    src = f.read()

anchor = "end\n\nend C1XiGlobalWeightedZeroSum"
assert src.count(anchor) == 1, "anchor not unique/found"

body = r'''-/! ### H-A1: analyticity of the weighted zero sum off the zero set

The (H) brick also needs the *function theory* of the weighted sum, not just
its summability: on a neighborhood of any point away from the zeros of
`completedRiemannXi`, the sum is holomorphic, with derivative the shell-ordered
weighted derivative sum.  This is the input of the removable-pole step (H-A2).

The summation is indexed in *shell order* (the sum over `m` of the finite
shell `m + 1`); the identity with the index-ordered sum of H-A0 follows from
`summable_of_shell_weight_tail_bound` and is proved in the (H) assembly as
`weightedRegularizedZeroSum_eq_sum_over_zeros` when the canonical identity is
assembled.  The shell order is the one that carries a *uniform* derivative
bound on the shell: on shell `n + 1` the denominator separation
`|Im s - Im rho| >= 2^n` is uniform in `s` as long as `s` stays in a fixed
horizontal strip. -/

/-- The weighted zero sum in shell-ordered form.  Each inner sum is finite
(one dyadic shell). -/
noncomputable def weightedRegularizedZeroSum (s : Complex) : Complex :=
  ∑' m : Nat, ∑' rho : spectralHeightShell (m + 1),
    weightedRegularizedZeroTerm s rho.1

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
    have hsub : HasDerivAt (fun s : Complex => s - rho.1) 1 s0 :=
      hasDerivAt_id.sub (hasDerivAt_const rho.1)
    simpa [← pow_two] using hsub.inv₀ hsr
  have hconst : HasDerivAt (fun s : Complex => (1 : ℂ) / rho.1) 0 s0 :=
    hasDerivAt_const _
  have hmain : HasDerivAt (fun s : Complex => (s - rho.1)⁻¹ + (1 : ℂ) / rho.1)
      (-(s0 - rho.1)⁻¹ ^ 2) s0 := hinv.add hconst
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
          rw [norm_inv, pow_two, inv_pow]
          field_simp [norm_ne_zero_iff.mpr hne]
          ring
    _ <= (xiMultiplicity rho : Real) / ((2 : Real) ^ n) ^ 2 := by
          have hsq : ((2 : Real) ^ n) ^ 2 <= ‖s - rho.1‖ ^ 2 := by
            simpa [pow_two] using (mul_le_mul (a := (2 : Real) ^ n)
              (b := (2 : Real) ^ n) (c := ‖s - rho.1‖) (d := ‖s - rho.1‖)
              hsp hsp (norm_nonneg _) (norm_nonneg _))
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
            (sq_pos_of_pos (pow_pos (by norm_num : (0 : Real) < 2) n)) hsq

/-- Every element of the source nontrivial zero set is a zero of the completed
xi function: the zero-set identification of `CC20ZetaCounting`. -/
lemma completedRiemannXi_eq_zero_of_mem_sourceNontrivialZeroSet
    {rho : sourceNontrivialZeroSet} : completedRiemannXi rho.1 = 0 :=
  (completedRiemannXi_eq_zero_iff_sourceNontrivialZero rho.1).mpr rho.2

/-- The shell-ordered sum splits at a dyadic height `N`: the prefix shells
`1 .. N` plus the shifted tail from `N + 1` upward.  Unconditional because
each inner shell sum is finite and the tail is dominated by the geometric
mass bound (brick G), which makes the whole layer sequence summable. -/
theorem weightedRegularizedZeroSum_split_shell (s : Complex) (N : Nat) :
    (∑' m : Nat, ∑' rho : spectralHeightShell (m + 1),
        weightedRegularizedZeroTerm s rho.1) =
      (∑ m in Finset.range N, ∑' rho : spectralHeightShell (m + 1),
        weightedRegularizedZeroTerm s rho.1) +
      (∑' m : Nat, ∑' rho : spectralHeightShell (m + N + 1),
        weightedRegularizedZeroTerm s rho.1) := by
  let L : Nat -> Complex := fun m =>
    ∑' rho : spectralHeightShell (m + 1), weightedRegularizedZeroTerm s rho.1
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
        ∑' rho : spectralHeightShell (m + 1), ‖weightedRegularizedZeroTerm s rho.1‖) := by
      exact (summable_nat_add_iff (f := fun k : Nat =>
        ∑' rho : spectralHeightShell k, ‖weightedRegularizedZeroTerm s rho.1‖)
        (k := 1)).mpr (by simpa using hpart.2)
    refine Summable.of_norm_bounded
      (fun m => ∑' rho : spectralHeightShell (m + 1),
        ‖weightedRegularizedZeroTerm s rho.1‖) hnormLayers ?_
    intro m
    letI := (spectralHeightShell_finite (m + 1)).fintype
    calc
      ‖∑' rho : spectralHeightShell (m + 1),
          weightedRegularizedZeroTerm s rho.1‖ =
          ‖∑ rho : spectralHeightShell (m + 1),
            weightedRegularizedZeroTerm s rho.1‖ := by
              rw [tsum_fintype]
      _ <= ∑ rho : spectralHeightShell (m + 1),
            ‖weightedRegularizedZeroTerm s rho.1‖ := by
              exact norm_sum_le _ _
      _ = ∑' rho : spectralHeightShell (m + 1),
            ‖weightedRegularizedZeroTerm s rho.1‖ := by
              rw [tsum_fintype]
  rw [tsum_eq_sum_range (f := L) N]
  dsimp [L]
  rfl

end

end C1XiGlobalWeightedZeroSum
end Source
end ConnesWeilRH
'''

out = src.replace(anchor, body, 1)
with path.open("w", encoding="utf-8") as f:
    f.write(out)
print("OK appended, new length:", len(out))
