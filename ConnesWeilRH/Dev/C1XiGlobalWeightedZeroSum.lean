import ConnesWeilRH.Dev.C1XiGlobalZeroSum
import ConnesWeilRH.Dev.C1SpectralSummability
import ConnesWeilRH.Dev.C1SpectralWeil

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

end

end C1XiGlobalWeightedZeroSum
end Source
end ConnesWeilRH

