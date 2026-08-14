import ConnesWeilRH.Dev.C1SpectralWeil
import ConnesWeilRH.Dev.C1SpectralSummability

/-!
# C1XiGlobalZeroSum - global regularized zero-sum machinery for Gate 2

The horizontal-edge bottom of Gate 2 is attacked through the canonical
regularized log-derivative identity for the completed Riemann xi function

```text
xi'/xi(s) = b + sum over ALL nontrivial zeros rho of ( 1/(s-rho) + 1/rho )
```

The right side can be bounded on a zero-free horizontal segment from the
closed dyadic shell multiplicity counts alone: near zeros contribute through
the closed finite principal part, and the far tail through the geometric
shell estimates below.  This module supplies the *global* summation facts:

- `regularizedZeroTerm`: the summand `1/(s-rho) + 1/rho` (bounded, unlike
  the raw `1/(s-rho)` term, which has no tail decay in the imaginary
  direction);
- `summable_of_shell_weight_tail_bound`: the free-prefix generalization of
  the closed `summable_of_shifted_geometric_shell_weight_bound` (the tail
  starts at shell index `n0` while the mass hypothesis runs from shell one);
- `regularizedZeroSummable`: unconditional summability of the regularized
  zero term over the whole zero set, from multiplicity growth `3^n` against
  denominator `4^n`;
- `regularizedZeroTail_norm_shellSum_le`: the quantitative value bound for
  the height-tail part of that sum, the concrete brick consumed by the
  horizontal-edge assembly.

No global product identity for `completedRiemannXi` is proved here (that is
the later `( H )` brick); this module is entirely classical summation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiGlobalZeroSum

open scoped BigOperators
open C1SpectralWeil
open C1SpectralSummability
open CC20YoshidaNearZeros

noncomputable section

/-- One summand of the globally regularized canonical zero sum.  The
regularization subtracts the constant `1/rho` so that the tail decays like
`|s| / (|rho| * |s - rho|)` instead of accumulating as `1/|Im rho|`. -/
noncomputable def regularizedZeroTerm (s : Complex)
    (rho : sourceNontrivialZeroSet) : Complex :=
  1 / (s - rho.1) + 1 / rho.1

/-- The regularization is subtracted-and-added algebra exactly:
`1/(s-rho) + 1/rho = s / (rho * (s - rho))`. -/
theorem regularizedZeroTerm_eq_div {s : Complex} {rho : sourceNontrivialZeroSet}
    (hrho : rho.1 ≠ 0) (hsr : s - rho.1 ≠ 0) :
    regularizedZeroTerm s rho = s / (rho.1 * (s - rho.1)) := by
  unfold regularizedZeroTerm
  field_simp [hrho, hsr]
  ring

/-- Free-prefix generalization of
`C1SpectralWeil.summable_of_shifted_geometric_shell_weight_bound`: the tail
sum may start at an arbitrary shell index `n0` (passing `n0 = 0` recovers
the original statement up to definitional equality of `0 + 1`).  The
geometric constant absorbs `q ^ n0` so the consumer only needs the plain
mass bound `mass (n + 1) <= K * q ^ n`. -/
theorem summable_of_shell_weight_tail_bound
    {alpha : Type*} (f weight : alpha -> Real) (shell : Nat -> Set alpha)
    (hf : forall x, 0 <= f x)
    (hpartition : forall x, ExistsUnique (fun n => x ∈ shell n))
    (hfinite : forall n, (shell n).Finite)
    {K B q : Real} {n0 : Nat} (hB : 0 <= B) (hq : 0 <= q) (hq4 : q < 4)
    (hmass : forall n,
      (∑' x : shell (n + 1), weight x) <= K * q ^ n)
    (hpoint : forall n, n0 <= n ->
      forall x : shell (n + 1),
        f x <= weight x * (B / ((2 : Real) ^ n) ^ 2)) :
    Summable f := by
  rw [summable_partition hf hpartition]
  constructor
  · intro n
    letI := (hfinite n).fintype
    exact (hasSum_fintype (fun x : shell n => f x)).summable
  · rw [← summable_nat_add_iff
      (f := fun n => ∑' x : shell n, f x) (n0 + 1)]
    have hratioNonneg : 0 <= q / 4 := div_nonneg hq (by norm_num)
    have hratioLt : q / 4 < 1 :=
      (div_lt_one (by norm_num : (0 : Real) < 4)).mpr hq4
    have hgeometric : Summable (fun n : Nat => (q / 4) ^ n) :=
      summable_geometric_of_lt_one hratioNonneg hratioLt
    refine Summable.of_nonneg_of_le
      (fun m => tsum_nonneg fun x => hf x) ?_
      (hgeometric.mul_left (K * B * (q / 4) ^ n0))
    intro m
    letI := (hfinite (m + n0 + 1)).fintype
    have hmassN := hmass (m + n0)
    rw [tsum_fintype] at hmassN
    rw [tsum_fintype]
    calc
      (∑ x : shell (m + n0 + 1), f x) <=
          ∑ x : shell (m + n0 + 1),
            weight x * (B / ((2 : Real) ^ (m + n0)) ^ 2) := by
              exact Finset.sum_le_sum fun x _hx =>
                hpoint (m + n0) (by omega) x
      _ = (∑ x : shell (m + n0 + 1), weight x) *
          (B / ((2 : Real) ^ (m + n0)) ^ 2) := by
            rw [Finset.sum_mul]
      _ <= (K * q ^ (m + n0)) * (B / ((2 : Real) ^ (m + n0)) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hmassN
              (div_nonneg hB (sq_nonneg _))
      _ = K * B * (q / 4) ^ n0 * (q / 4) ^ m := by
            rw [pow_two]
            have hfour :
                (2 : Real) ^ (m + n0) * (2 : Real) ^ (m + n0) =
                  4 ^ (m + n0) := by
              rw [← mul_pow]
              norm_num
            rw [hfour]
            rw [pow_add]
            rw [div_pow, div_pow]
            ring_nf

/-- Height-shell lower bound on the imaginary coordinate: an element of shell
`n + 1` has `|Im rho| >= 2 ^ (n + 1)`. -/
theorem shell_lower_im {n : Nat} {rho : sourceNontrivialZeroSet}
    (hrho : rho ∈ spectralHeightShell (n + 1)) :
    (2 : Real) ^ (n + 1) <= |rho.1.im| := by
  exact pow_succ_le_of_dyadicShellIndex_eq_succ
    (by simpa [spectralHeightShell] using hrho)

/-- Norm bound for one regularized zero term inside shell `n + 1`: the
`|s - rho| >= 2 ^ n` separation uses only the height shell and the dyadic
bound `|Im s| < 2 ^ n0` with `n0 <= n`. -/
theorem regularizedZeroTerm_norm_le (s : Complex)
    (n n0 : Nat) (hn : n0 <= n) (hs_lt : |s.im| < (2 : Real) ^ n0)
    {rho : sourceNontrivialZeroSet}
    (hrho : rho ∈ spectralHeightShell (n + 1)) :
    ‖regularizedZeroTerm s rho‖ <=
      ‖s‖ / ((2 : Real) ^ (n + 1) * (2 : Real) ^ n) := by
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
  have hseparation : (2 : Real) ^ n <= |rho.1.im - s.im| := by
    nlinarith [him, hsm, hpowThrough, hdist_abs,
      pow_nonneg (by norm_num : (0 : Real) <= 2) n]
  have hsp : (2 : Real) ^ n <= ‖s - rho.1‖ := by
    calc
      (2 : Real) ^ n <= |rho.1.im - s.im| := hseparation
      _ = |(s - rho.1).im| := by
        simpa using (abs_sub_comm rho.1.im s.im)
      _ <= ‖s - rho.1‖ := Complex.abs_im_le_norm (s - rho.1)
  have hsr_ne : s - rho.1 ≠ 0 := by
    intro hz
    have : ‖s - rho.1‖ = 0 := by simp [hz]
    nlinarith [hsp, this,
      pow_pos (by norm_num : (0 : Real) < 2) n]
  have hdiv := regularizedZeroTerm_eq_div (s := s) (rho := rho)
    hrho_nonzero hsr_ne
  rw [hdiv]
  calc
    ‖s / (rho.1 * (s - rho.1))‖ =
        ‖s‖ / (‖rho.1‖ * ‖s - rho.1‖) := by
          simp only [norm_div, norm_mul]
    _ <= ‖s‖ / ((2 : Real) ^ (n + 1) * (2 : Real) ^ n) := by
          have hrho_norm : (2 : Real) ^ (n + 1) <= ‖rho.1‖ :=
            le_trans him (Complex.abs_im_le_norm rho.1)
          have hdenBound :
              (2 : Real) ^ (n + 1) * (2 : Real) ^ n <=
                ‖rho.1‖ * ‖s - rho.1‖ :=
            mul_le_mul hrho_norm hsp
              (pow_nonneg (by norm_num : (0 : Real) <= 2) n)
              (norm_nonneg _)
          exact div_le_div_of_nonneg_left (norm_nonneg s)
            (mul_pos (pow_pos (by norm_num : (0 : Real) < 2) (n + 1))
              (pow_pos (by norm_num : (0 : Real) < 2) n))
            hdenBound

/-- Multiplicity-inflated pointwise instance of the tail weight bound:
`||term|| <= mult * (2 * ||s|| / 4 ^ n)`.  The multiplicity factor is at
least one, so the atom `1 / 4 ^ n` decay is preserved. -/
theorem regularizedZeroTerm_norm_instance (s : Complex)
    (n n0 : Nat) (hn : n0 <= n) (hs_lt : |s.im| < (2 : Real) ^ n0)
    {rho : sourceNontrivialZeroSet}
    (hrho : rho ∈ spectralHeightShell (n + 1)) :
    ‖regularizedZeroTerm s rho‖ <=
      (xiMultiplicity rho : Real) *
        (2 * ‖s‖ / ((2 : Real) ^ n) ^ 2) := by
  have hbasis := regularizedZeroTerm_norm_le s n n0 hn hs_lt hrho
  have halg : ‖s‖ / ((2 : Real) ^ (n + 1) * (2 : Real) ^ n) <=
      (2 * ‖s‖) / ((2 : Real) ^ n) ^ 2 := by
    rw [pow_two]
    have hfour : (2 : Real) ^ n * (2 : Real) ^ n = 4 ^ n := by
      rw [← mul_pow]
      norm_num
    rw [pow_succ, hfour]
    have hsym : ((2 : Real) ^ n * 2) * (2 : Real) ^ n =
        2 * (4 : Real) ^ n := by
      calc
        ((2 : Real) ^ n * 2) * (2 : Real) ^ n =
            2 * ((2 : Real) ^ n * (2 : Real) ^ n) := by
              ring
        _ = 2 * (4 : Real) ^ n := by rw [hfour]
    rw [hsym]
    have hposX : 0 < 2 * (4 : Real) ^ n := by positivity
    have hposY : 0 < (4 : Real) ^ n := by positivity
    rw [div_le_div_iff₀ hposX hposY]
    ring_nf
    have hnonneg : 0 <= ‖s‖ * (4 : Real) ^ n :=
      mul_nonneg (norm_nonneg s)
        (le_of_lt (pow_pos (by norm_num : (0 : Real) < 4) n))
    nlinarith
  have hmult : 1 <= (xiMultiplicity rho : Real) := by
    exact_mod_cast (Nat.succ_le_of_lt (xiMultiplicity_pos rho))
  have hfactor : 0 <= (2 * ‖s‖) / ((2 : Real) ^ n) ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2)
      (norm_nonneg s)) (sq_nonneg _)
  exact le_trans (le_trans hbasis halg)
    (by simpa [one_mul] using mul_le_mul_of_nonneg_right hmult hfactor)

/-- The globally regularized zero sum is unconditionally summable at every
`Complex` point, for every `2 ^ n0` dyadic height bound on `|Im s|`. -/
theorem regularizedZeroSummable (s : Complex) :
    Summable (fun rho : sourceNontrivialZeroSet =>
      regularizedZeroTerm s rho) := by
  apply Summable.of_norm
  let n0 : Nat := dyadicShellIndex |s.im| + 1
  have hs_lt : |s.im| < (2 : Real) ^ n0 := by
    dsimp only [n0]
    exact lt_two_pow_succ_dyadicShellIndex |s.im|
  exact summable_of_shell_weight_tail_bound
    (f := fun rho => ‖regularizedZeroTerm s rho‖)
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
      regularizedZeroTerm_norm_instance s n n0 hn hs_lt x.2)

/-- Quantitative value bound for the height-tail of the regularized zero
sum: everything from shell `n0 + 1` upward contributes at most
`4 * 2 * ||s|| * K * (3/4)^n0`, from the geometric shell mass
`mass (n+1) <= K * 3^n` against denominator `4^n`. -/
theorem regularizedZeroTail_norm_shellSum_le (s : Complex) (n0 : Nat)
    (hs_lt : |s.im| < (2 : Real) ^ n0) :
    (∑' m : Nat, ∑' rho : spectralHeightShell (m + n0 + 1),
      ‖regularizedZeroTerm s rho.1‖) <=
      4 * (2 * ‖s‖) * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 := by
  have hnormSum : Summable (fun rho : sourceNontrivialZeroSet =>
      ‖regularizedZeroTerm s rho‖) := by
    -- the norm version of the summability proof (same instance as the
    -- term version, without the `of_norm` step)
    let n : Nat := dyadicShellIndex |s.im| + 1
    have hs0 : |s.im| < (2 : Real) ^ n := by
      dsimp only [n]
      exact lt_two_pow_succ_dyadicShellIndex |s.im|
    exact summable_of_shell_weight_tail_bound
      (f := fun rho => ‖regularizedZeroTerm s rho‖)
      (weight := fun rho => (xiMultiplicity rho : Real))
      (shell := spectralHeightShell)
      (hf := fun rho => norm_nonneg _)
      (hpartition := spectralHeightShell_partition)
      (hfinite := spectralHeightShell_finite)
      (K := spectralMultiplicityConstant) (B := 2 * ‖s‖) (q := 3)
      (n0 := n)
      (hB := mul_nonneg (by norm_num : (0 : Real) <= 2) (norm_nonneg s))
      (hq := by norm_num) (hq4 := by norm_num)
      (hmass := fun m => by
        simpa [spectralHeightMultiplicity] using
          spectralHeightMultiplicity_geometric_bound m)
      (hpoint := fun m hm x =>
        regularizedZeroTerm_norm_instance s m n hm hs0 x.2)
  have hpartitionSum :
      (∀ n : Nat, Summable (fun x : spectralHeightShell n =>
          ‖regularizedZeroTerm s x.1‖)) ∧
        Summable (fun n : Nat => ∑' x : spectralHeightShell n,
          ‖regularizedZeroTerm s x.1‖) :=
    (summable_partition (fun rho : sourceNontrivialZeroSet =>
        norm_nonneg _) spectralHeightShell_partition).mp hnormSum
  have htailSum : Summable (fun m : Nat =>
      ∑' rho : spectralHeightShell (m + n0 + 1),
        ‖regularizedZeroTerm s rho.1‖) := by
    refine (summable_nat_add_iff
      (f := fun k : Nat => ∑' x : spectralHeightShell k,
        ‖regularizedZeroTerm s x.1‖) (n0 + 1)).mpr hpartitionSum.2
  have hperM (m : Nat) :
      (∑' rho : spectralHeightShell (m + n0 + 1),
        ‖regularizedZeroTerm s rho.1‖) <=
        spectralMultiplicityConstant * (2 * ‖s‖) *
          (3 / 4 : Real) ^ (m + n0) := by
    letI := (spectralHeightShell_finite (m + n0 + 1)).fintype
    have hmassN' : (∑' rho : spectralHeightShell (m + n0 + 1),
        (xiMultiplicity rho.1 : Real)) <=
        spectralMultiplicityConstant * 3 ^ (m + n0) := by
      simpa [spectralHeightMultiplicity] using
        spectralHeightMultiplicity_geometric_bound (m + n0)
    have hmassN : (∑ rho : spectralHeightShell (m + n0 + 1),
        (xiMultiplicity rho.1 : Real)) <=
        spectralMultiplicityConstant * 3 ^ (m + n0) := by
      rw [tsum_fintype] at hmassN'
      exact hmassN'
    rw [tsum_fintype]
    calc
      (∑ rho : spectralHeightShell (m + n0 + 1),
          ‖regularizedZeroTerm s rho.1‖) <=
          ∑ rho : spectralHeightShell (m + n0 + 1),
            (xiMultiplicity rho.1 : Real) *
              (2 * ‖s‖ / ((2 : Real) ^ (m + n0)) ^ 2) := by
                exact Finset.sum_le_sum fun x _hx =>
                  regularizedZeroTerm_norm_instance s (m + n0) n0
                    (by omega) hs_lt x.2
      _ = (∑ rho : spectralHeightShell (m + n0 + 1),
            (xiMultiplicity rho.1 : Real)) *
          (2 * ‖s‖ / ((2 : Real) ^ (m + n0)) ^ 2) := by
            rw [Finset.sum_mul]
      _ <= spectralMultiplicityConstant * 3 ^ (m + n0) *
          (2 * ‖s‖ / ((2 : Real) ^ (m + n0)) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hmassN
              (div_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2)
                (norm_nonneg s)) (sq_nonneg _))
      _ = spectralMultiplicityConstant * (2 * ‖s‖) *
          (3 / 4 : Real) ^ (m + n0) := by
            rw [pow_two]
            have hfour :
                (2 : Real) ^ (m + n0) * (2 : Real) ^ (m + n0) =
                  4 ^ (m + n0) := by
              rw [← mul_pow]
              norm_num
            rw [hfour]
            rw [div_pow]
            ring
  have hgeoConst : Summable (fun m : Nat =>
      spectralMultiplicityConstant * (2 * ‖s‖) *
        (3 / 4 : Real) ^ (m + n0)) := by
    have hgeo : Summable (fun m : Nat => (3 / 4 : Real) ^ m) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using
      hgeo.mul_left (spectralMultiplicityConstant * (2 * ‖s‖) *
        (3 / 4 : Real) ^ n0)
  calc
    (∑' m : Nat, ∑' rho : spectralHeightShell (m + n0 + 1),
        ‖regularizedZeroTerm s rho.1‖) <=
        ∑' m : Nat,
          spectralMultiplicityConstant * (2 * ‖s‖) *
            (3 / 4 : Real) ^ (m + n0) := by
              exact (htailSum.tsum_le_tsum (fun m => hperM m) hgeoConst)
    _ = ∑' m : Nat,
          (spectralMultiplicityConstant * (2 * ‖s‖) * (3 / 4 : Real) ^ n0) *
            (3 / 4 : Real) ^ m := by
              refine tsum_congr (fun m => ?_)
              rw [pow_add]
              ring
    _ = spectralMultiplicityConstant * (2 * ‖s‖) *
        (3 / 4 : Real) ^ n0 * ∑' m : Nat, (3 / 4 : Real) ^ m := by
          rw [tsum_mul_left]
    _ = 4 * (2 * ‖s‖) * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
          ring_nf

end

end C1XiGlobalZeroSum
end Source
end ConnesWeilRH