import ConnesWeilRH.Dev.C1SpectralWeil
import ConnesWeilRH.Dev.C1SpectralSummability

/-!
# C1RouteAWeightedZeroMeasure

The first executable brick for Route-A grandchild A.005.1.  The omitted
low-shell spectral residual is bounded by a fixed, owner-preserving weight:
the norm of the actual multiplicity-weighted spectral term.  This is only a
residual reduction; it does not assert that the resulting weight budget is
small enough for the producer.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAWeightedZeroMeasure

open C1SpectralWeil
open C1SpectralSummability
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

/-- Local spelling of the exact low-shell owner, kept here so this brick does
not depend on the larger residual consumer during its focused audit. -/
noncomputable def weightedZeroMeasureShellPrefix (N : Nat) :
    Finset CC20YoshidaNearZeros.sourceNontrivialZeroSet :=
  (Finset.range N).biUnion fun k => (spectralHeightShell_finite k).toFinset

/-- Fixed nonnegative weight attached to the same test and source-zero owner.
It is not fitted to a sampled sign or to a replacement prime owner. -/
noncomputable def weightedZeroMeasure
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet) : Real :=
  spectralNormTerm F rho

theorem weightedZeroMeasure_nonneg
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet) :
    0 ≤ weightedZeroMeasure F rho := by
  exact spectralNormTerm_nonnegative F rho

/-- The fixed weight controls the real part of each actual spectral term. -/
theorem spectralTerm_re_le_weightedZeroMeasure
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet) :
    (spectralTerm F rho).re ≤ weightedZeroMeasure F rho := by
  change (spectralTerm F rho).re ≤ spectralNormTerm F rho
  exact (Complex.re_le_norm (spectralTerm F rho)).trans_eq
    (norm_spectralTerm F rho)

/-- The omitted low-shell residual is reduced to an explicit weighted-zero
measure budget, with no change to the source-zero owner. -/
theorem finite_prefix_residual_re_le_weightedZeroMeasure
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest) (N : Nat)
    (S : Finset CC20YoshidaNearZeros.sourceNontrivialZeroSet) :
    (∑ z ∈ weightedZeroMeasureShellPrefix N \ S, spectralTerm F z).re ≤
      ∑ z ∈ weightedZeroMeasureShellPrefix N \ S, weightedZeroMeasure F z := by
  calc
    (∑ z ∈ weightedZeroMeasureShellPrefix N \ S, spectralTerm F z).re =
        ∑ z ∈ weightedZeroMeasureShellPrefix N \ S, (spectralTerm F z).re := by
      simp
    _ ≤ ∑ z ∈ weightedZeroMeasureShellPrefix N \ S, weightedZeroMeasure F z := by
      exact Finset.sum_le_sum fun z hz =>
        spectralTerm_re_le_weightedZeroMeasure F z

/-- A local enclosure may price the exact weight through two independent
factors: an analytic-multiplicity bound and a transform-norm bound.  Keeping
the factors separate is essential for the later closed-ball certificate; no
replacement owner or fitted multiplicity is introduced here. -/
theorem weightedZeroMeasure_le_mul_of_multiplicity_le
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet)
    {Mmult Meval : Real}
    (hMmult : (xiMultiplicity rho : Real) ≤ Mmult)
    (hMeval : norm (CC20YoshidaConvolution.CompactLogTest.laplaceAt F
        (centeredXiCoordinate rho)) ≤ Meval)
    (hMmult_nonneg : 0 ≤ Mmult) (hMeval_nonneg : 0 ≤ Meval) :
    weightedZeroMeasure F rho ≤ Mmult * Meval := by
  unfold weightedZeroMeasure spectralNormTerm
  calc
    (xiMultiplicity rho : Real) *
        norm (CC20YoshidaConvolution.CompactLogTest.laplaceAt F
          (centeredXiCoordinate rho)) ≤
        Mmult * norm (CC20YoshidaConvolution.CompactLogTest.laplaceAt F
          (centeredXiCoordinate rho)) := by
      exact mul_le_mul_of_nonneg_right hMmult (norm_nonneg _)
    _ ≤ Mmult * Meval := by
      exact mul_le_mul_of_nonneg_left hMeval hMmult_nonneg

/-- Finite-owner aggregation of the factor split.  The shell itself remains a
Finset of the actual source-zero subtype; only the two named local bounds are
abstracted. -/
theorem finite_weightedZeroMeasure_sum_le_card_mul
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (S : Finset CC20YoshidaNearZeros.sourceNontrivialZeroSet)
    {Mmult Meval : Real}
    (hMmult : ∀ rho ∈ S, (xiMultiplicity rho : Real) ≤ Mmult)
    (hMeval : ∀ rho ∈ S,
      norm (CC20YoshidaConvolution.CompactLogTest.laplaceAt F
        (centeredXiCoordinate rho)) ≤ Meval)
    (hMmult_nonneg : 0 ≤ Mmult) (hMeval_nonneg : 0 ≤ Meval) :
    ∑ rho ∈ S, weightedZeroMeasure F rho ≤
      (S.card : Real) * (Mmult * Meval) := by
  calc
    ∑ rho ∈ S, weightedZeroMeasure F rho ≤
        ∑ _rho ∈ S, Mmult * Meval := by
      exact Finset.sum_le_sum fun rho hrho =>
        weightedZeroMeasure_le_mul_of_multiplicity_le F rho
          (hMmult rho hrho) (hMeval rho hrho) hMmult_nonneg hMeval_nonneg
    _ = (S.card : Real) * (Mmult * Meval) := by
      simp [Nat.cast_ofNat]

/-- The existing quadratic vertical Laplace estimate prices one exact dyadic
shell of the weighted-zero budget by its analytic multiplicity mass. -/
theorem exists_spectralHeightShell_weightedZeroMeasure_bound
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    ∃ B : Real, 0 ≤ B ∧ ∀ n : Nat,
      (∑ rho ∈ (spectralHeightShell_finite (n + 1)).toFinset,
        weightedZeroMeasure F rho) ≤
      spectralHeightMultiplicity (n + 1) *
          (B / ((2 : Real) ^ n) ^ 2) := by
  obtain ⟨B, hB, hpoint⟩ := exists_spectral_laplaceAt_dyadic_tail_bound F
  refine ⟨B, hB, ?_⟩
  intro n
  let shell := spectralHeightShell (n + 1)
  let hfinite : shell.Finite := spectralHeightShell_finite (n + 1)
  letI := hfinite.fintype
  have hmass : spectralHeightMultiplicity (n + 1) =
      ∑ rho ∈ hfinite.toFinset, (xiMultiplicity rho : Real) := by
    simpa only [spectralHeightMultiplicity, shell] using
      (tsum_finite_subtype_eq_sum_toFinset hfinite
        (fun rho => (xiMultiplicity rho : Real)))
  have hpoint' : ∀ rho : shell,
      weightedZeroMeasure F rho.1 ≤
        (xiMultiplicity rho.1 : Real) *
          (B / ((2 : Real) ^ n) ^ 2) := by
    intro rho
    unfold weightedZeroMeasure spectralNormTerm
    exact mul_le_mul_of_nonneg_left (hpoint n rho)
      (Nat.cast_nonneg (xiMultiplicity rho.1))
  rw [hmass]
  calc
    (∑ rho ∈ hfinite.toFinset, weightedZeroMeasure F rho) ≤
        ∑ rho ∈ hfinite.toFinset, (xiMultiplicity rho : Real) *
          (B / ((2 : Real) ^ n) ^ 2) := by
      exact Finset.sum_le_sum fun rho hrho => hpoint'
        ⟨rho, hfinite.mem_toFinset.mp hrho⟩
    _ = (∑ rho ∈ hfinite.toFinset, (xiMultiplicity rho : Real)) *
          (B / ((2 : Real) ^ n) ^ 2) := by
      rw [Finset.sum_mul]

/-- The existing xi-growth count turns the exact-shell estimate into an
explicit geometric weighted-zero budget.  The ratio is 3/4: the multiplicity
growth contributes 3^n while the quadratic vertical estimate contributes
4^(-n). -/
theorem exists_geometric_spectralHeightShell_weightedZeroMeasure_bound
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    ∃ B : Real, 0 ≤ B ∧ ∀ n : Nat,
      (∑ rho ∈ (spectralHeightShell_finite (n + 1)).toFinset,
        weightedZeroMeasure F rho) ≤
      spectralMultiplicityConstant * B * ((3 : Real) / 4) ^ n := by
  obtain ⟨B, hB, hshell⟩ :=
    exists_spectralHeightShell_weightedZeroMeasure_bound F
  refine ⟨B, hB, ?_⟩
  intro n
  calc
    (∑ rho ∈ (spectralHeightShell_finite (n + 1)).toFinset,
        weightedZeroMeasure F rho) ≤
        spectralHeightMultiplicity (n + 1) *
          (B / ((2 : Real) ^ n) ^ 2) := hshell n
    _ ≤ (spectralMultiplicityConstant * (3 : Real) ^ n) *
          (B / ((2 : Real) ^ n) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (spectralHeightMultiplicity_geometric_bound n)
        (div_nonneg hB (sq_nonneg _))
    _ = spectralMultiplicityConstant * B * ((3 : Real) / 4) ^ n := by
      rw [div_pow]
      norm_num [pow_two, mul_pow]
      have hfour :
          (2 : Real) ^ n * (2 : Real) ^ n = 4 ^ n := by
        rw [← mul_pow]
        norm_num
      rw [hfour]
      ring

/-! The next quantitative interface is scalar, not complex-valued: the
weighted-zero budget must itself be summable before a finite-owner enclosure
can separate a certified prefix from a certified tail.  The existing
quadratic vertical estimate and multiplicity-shell consumer provide exactly
that implication, while retaining the actual source-zero owner. -/

theorem weightedZeroMeasure_summable_of_geometric_heightMultiplicity_bound
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    {K q : Real} (hq : 0 ≤ q) (hq4 : q < 4)
    (hmass : ∀ n,
      spectralHeightMultiplicity (n + 1) ≤ K * q ^ n) :
    Summable (weightedZeroMeasure F) := by
  have hcomplex : Summable (spectralTerm F) :=
    spectralSummable_of_geometric_heightMultiplicity_bound
      F hq hq4 hmass
  have hnorm : Summable (fun rho => norm (spectralTerm F rho)) :=
    hcomplex.norm
  simpa only [norm_spectralTerm, weightedZeroMeasure] using hnorm

/-- The geometric shell budget closes absolute summability for the actual
weighted-zero measure, with no new multiplicity hypothesis. -/
theorem weightedZeroMeasure_summable_of_existing_xi_growth
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    Summable (weightedZeroMeasure F) := by
  apply weightedZeroMeasure_summable_of_geometric_heightMultiplicity_bound
    (K := spectralMultiplicityConstant) (q := 3) F (by norm_num) (by norm_num)
  exact spectralHeightMultiplicity_geometric_bound

/-- The high-shell weighted-zero tail has one explicit scalar budget.  This
is the geometric-series assembly of the exact-owner shell estimates; shell
zero remains a separate finite prefix in the producer. -/
theorem exists_weightedZeroMeasure_highShell_tsum_bound
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    ∃ B : Real, 0 ≤ B ∧
      (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        weightedZeroMeasure F rho.1) ≤
      4 * spectralMultiplicityConstant * B := by
  obtain ⟨B, hB, hshell⟩ :=
    exists_geometric_spectralHeightShell_weightedZeroMeasure_bound F
  refine ⟨B, hB, ?_⟩
  let r : Real := (3 : Real) / 4
  let K : Real := spectralMultiplicityConstant * B
  have hK : 0 ≤ K := mul_nonneg spectralMultiplicityConstant_nonneg hB
  have hr0 : 0 ≤ r := by
    dsimp [r]
    norm_num
  have hr1 : r < 1 := by
    dsimp [r]
    norm_num
  have hgeo : Summable (fun n : Nat => K * r ^ n) := by
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left K
  have hbound : ∀ n : Nat,
      (∑' rho : spectralHeightShell (n + 1),
        weightedZeroMeasure F rho.1) ≤ K * r ^ n := by
    intro n
    let shell := spectralHeightShell (n + 1)
    let hfinite : shell.Finite := spectralHeightShell_finite (n + 1)
    have hsum :
        (∑' rho : shell, weightedZeroMeasure F rho.1) =
          ∑ rho ∈ hfinite.toFinset, weightedZeroMeasure F rho := by
      exact tsum_finite_subtype_eq_sum_toFinset hfinite
        (fun rho => weightedZeroMeasure F rho)
    rw [hsum]
    dsimp [K, r]
    exact hshell n
  have htailSummable :
      Summable (fun n : Nat =>
        ∑' rho : spectralHeightShell (n + 1),
          weightedZeroMeasure F rho.1) := by
    refine Summable.of_nonneg_of_le
      (fun n => tsum_nonneg (fun rho => weightedZeroMeasure_nonneg F rho.1))
      hbound hgeo
  have htail := htailSummable.tsum_le_tsum hbound hgeo
  calc
    (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        weightedZeroMeasure F rho.1) ≤ ∑' n : Nat, K * r ^ n := htail
    _ = K * (∑' n : Nat, r ^ n) := by rw [tsum_mul_left]
    _ = K * (1 / (1 - r)) := by
      rw [tsum_geometric_of_lt_one hr0 hr1]
      simp only [one_div]
    _ = 4 * spectralMultiplicityConstant * B := by
      dsimp [K, r]
      norm_num
      ring

end
end C1RouteAWeightedZeroMeasure
end Source
end ConnesWeilRH
