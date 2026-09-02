import ConnesWeilRH.Dev.C1HealthyYoshidaClosedPrefix
import ConnesWeilRH.Dev.C1SpectralTailBound

/-!
# C1HealthyYoshidaSpectralNegativity - finite prefix plus spectral tail

This module joins the finite closed-ball sign ledger to the fourth-order
spectral tail bound.  Shell order is used only as the exact partition owner
for the absolutely summable source-zero spectrum; it does not choose or
duplicate any zeros.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaSpectralNegativity

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaDetector
open C1HealthyYoshidaUnscaledOrbit
open C1HealthyYoshidaClosedPrefix
open C1SpectralSummability
open C1SpectralTailBound
open C1SpectralWeil
open scoped BigOperators

noncomputable section

/-- The finite union of all height shells strictly below `N`.  This owner is
used instead of a closed height interval so a zero lying exactly on a dyadic
boundary belongs to the high-shell tail exactly once. -/
noncomputable def spectralHeightShellPrefix (N : Nat) :
    Finset sourceNontrivialZeroSet :=
  (Finset.range N).biUnion fun k => (spectralHeightShell_finite k).toFinset

theorem mem_spectralHeightShellPrefix_iff
    (N : Nat) (rho : sourceNontrivialZeroSet) :
    rho ∈ spectralHeightShellPrefix N ↔
      dyadicShellIndex |rho.1.im| < N := by
  classical
  constructor
  · intro hmem
    rw [spectralHeightShellPrefix, Finset.mem_biUnion] at hmem
    rcases hmem with ⟨k, hk, hrho⟩
    have hshell : rho ∈ spectralHeightShell k :=
      (spectralHeightShell_finite k).mem_toFinset.mp hrho
    have hindex : dyadicShellIndex |rho.1.im| = k := by
      simpa only [spectralHeightShell, Set.mem_setOf_eq] using hshell
    simpa only [hindex] using Finset.mem_range.mp hk
  · intro hindex
    rw [spectralHeightShellPrefix, Finset.mem_biUnion]
    refine ⟨dyadicShellIndex |rho.1.im|, Finset.mem_range.mpr hindex, ?_⟩
    apply (spectralHeightShell_finite _).mem_toFinset.mpr
    exact rfl

/-- Every low-shell zero lies in the corresponding finite height window.
The strict shell upper bound is what prevents a dyadic boundary zero from
entering this prefix. -/
theorem spectralHeightShellPrefix_subset_finiteHeightZeros (N : Nat) :
    spectralHeightShellPrefix N ⊆ finiteHeightZeros ((2 : Real) ^ N) := by
  intro rho hrho
  rw [mem_finiteHeightZeros_iff]
  have hindex : dyadicShellIndex |rho.1.im| < N :=
    (mem_spectralHeightShellPrefix_iff N rho).mp hrho
  have hshellUpper := lt_two_pow_succ_dyadicShellIndex |rho.1.im|
  have hpow : (2 : Real) ^ (dyadicShellIndex |rho.1.im| + 1) ≤
      (2 : Real) ^ N :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hindex)
  exact hshellUpper.le.trans hpow

/-- Reading the finite low-shell owner as a finset sum agrees with its
shell-ordered presentation. -/
theorem sum_spectralHeightShellPrefix_eq_shell_prefix
    (F : CompactLogTest) (N : Nat) :
    (∑ rho ∈ spectralHeightShellPrefix N, spectralTerm F rho) =
      ∑ k ∈ Finset.range N, ∑' rho : spectralHeightShell k,
        spectralTerm F rho.1 := by
  classical
  have hdisjoint :
      Set.PairwiseDisjoint (↑(Finset.range N) : Set Nat)
        (fun k => (spectralHeightShell_finite k).toFinset) := by
    intro i hi j hj hij
    refine Finset.disjoint_left.mpr ?_
    intro rho hrhoi hrhoj
    have hshellI : rho ∈ spectralHeightShell i :=
      (spectralHeightShell_finite i).mem_toFinset.mp hrhoi
    have hshellJ : rho ∈ spectralHeightShell j :=
      (spectralHeightShell_finite j).mem_toFinset.mp hrhoj
    have hindexI : dyadicShellIndex |rho.1.im| = i := by
      simpa only [spectralHeightShell, Set.mem_setOf_eq] using hshellI
    have hindexJ : dyadicShellIndex |rho.1.im| = j := by
      simpa only [spectralHeightShell, Set.mem_setOf_eq] using hshellJ
    exact hij (hindexI.symm.trans hindexJ)
  rw [spectralHeightShellPrefix, Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro k _hk
  letI := (spectralHeightShell_finite k).fintype
  rw [tsum_fintype]
  apply Finset.sum_subtype
  intro rho
  exact (spectralHeightShell_finite k).mem_toFinset

/-- The shell-ordered spectrum is the original source-indexed spectrum.
The reindexing is the exact unique `spectralHeightShell` partition. -/
theorem spectralHeightShellSum_eq_source_tsum (F : CompactLogTest) :
    (∑' m : Nat, ∑' rho : spectralHeightShell m,
      spectralTerm F rho.1) =
      ∑' rho : sourceNontrivialZeroSet, spectralTerm F rho := by
  let e := Set.sigmaEquiv spectralHeightShell spectralHeightShell_partition
  have hsource : Summable (fun rho : sourceNontrivialZeroSet =>
      spectralTerm F rho) := spectralSummable F
  have hsigma : Summable (fun p : Sigma fun m => spectralHeightShell m =>
      spectralTerm F p.2.1) := by
    simpa only [e, Function.comp_apply] using e.summable_iff.mpr hsource
  calc
    (∑' m : Nat, ∑' rho : spectralHeightShell m,
        spectralTerm F rho.1) =
        ∑' p : Sigma fun m => spectralHeightShell m, spectralTerm F p.2.1 := by
          symm
          simpa only using hsigma.tsum_sigma
    _ = ∑' rho : sourceNontrivialZeroSet, spectralTerm F rho := by
      simpa only [e, Set.sigmaEquiv, Function.comp_apply] using
        e.tsum_eq (fun rho : sourceNontrivialZeroSet => spectralTerm F rho)

/-- The complex spectral shell layers are summable because their norms are
dominated by the already-proved nonnegative partition of the absolute spectrum. -/
theorem spectralHeightShellLayerSummable (F : CompactLogTest) :
    Summable (fun m : Nat => ∑' rho : spectralHeightShell m,
      spectralTerm F rho.1) := by
  have hnorm : Summable (fun rho : sourceNontrivialZeroSet =>
      ‖spectralTerm F rho‖) := (spectralSummable F).norm
  have hpart := (summable_partition
    (f := fun rho : sourceNontrivialZeroSet => ‖spectralTerm F rho‖)
    (hf := fun rho => norm_nonneg _) spectralHeightShell_partition).mp hnorm
  have hnormLayers : Summable (fun m : Nat =>
      ∑' rho : spectralHeightShell m, ‖spectralTerm F rho.1‖) := by
    simpa using hpart.2
  refine Summable.of_norm_bounded hnormLayers ?_
  intro m
  letI := (spectralHeightShell_finite m).fintype
  calc
    ‖∑' rho : spectralHeightShell m, spectralTerm F rho.1‖ =
        ‖∑ rho : spectralHeightShell m, spectralTerm F rho.1‖ := by
          rw [tsum_fintype]
    _ ≤ ∑ rho : spectralHeightShell m, ‖spectralTerm F rho.1‖ :=
      norm_sum_le _ _
    _ = ∑' rho : spectralHeightShell m, ‖spectralTerm F rho.1‖ := by
      rw [tsum_fintype]

/-- The shell-ordered spectral sum splits into its first `N` shells and the
tail beginning at shell `N`. -/
theorem spectralHeightShellSum_split (F : CompactLogTest) (N : Nat) :
    (∑' m : Nat, ∑' rho : spectralHeightShell m,
      spectralTerm F rho.1) =
      (∑ m ∈ Finset.range N, ∑' rho : spectralHeightShell m,
        spectralTerm F rho.1) +
      (∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        spectralTerm F rho.1) := by
  let L : Nat -> Complex := fun m =>
    ∑' rho : spectralHeightShell m, spectralTerm F rho.1
  simpa [L] using (spectralHeightShellLayerSummable F).sum_add_tsum_nat_add N |>.symm

/-- The real part of the complex high-shell tail is bounded by the same
tail with norms taken before summation. -/
theorem spectralHeightShellTail_re_le_normTail
    (F : CompactLogTest) (N : Nat) :
    (∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
      spectralTerm F rho.1).re ≤
      ∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        ‖spectralTerm F rho.1‖ := by
  have hterms := spectralHeightShellLayerSummable F
  have htailTerms : Summable (fun m : Nat =>
      ∑' rho : spectralHeightShell (m + N), spectralTerm F rho.1) :=
    (summable_nat_add_iff
      (f := fun k : Nat => ∑' rho : spectralHeightShell k,
        spectralTerm F rho.1) N).mpr hterms
  have hnorm : Summable (fun rho : sourceNontrivialZeroSet =>
      ‖spectralTerm F rho‖) := (spectralSummable F).norm
  have hpart := (summable_partition
    (f := fun rho : sourceNontrivialZeroSet => ‖spectralTerm F rho‖)
    (hf := fun rho => norm_nonneg _) spectralHeightShell_partition).mp hnorm
  have htailNorms : Summable (fun m : Nat =>
      ∑' rho : spectralHeightShell (m + N), ‖spectralTerm F rho.1‖) :=
    (summable_nat_add_iff
      (f := fun k : Nat => ∑' rho : spectralHeightShell k,
        ‖spectralTerm F rho.1‖) N).mpr hpart.2
  have hinner (m : Nat) :
      ‖∑' rho : spectralHeightShell (m + N), spectralTerm F rho.1‖ ≤
        ∑' rho : spectralHeightShell (m + N), ‖spectralTerm F rho.1‖ :=
    norm_tsum_le_tsum_norm ((spectralSummable F).norm.subtype _)
  calc
    (∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        spectralTerm F rho.1).re ≤
        |(∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
          spectralTerm F rho.1).re| := le_abs_self _
    _ ≤ ‖∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        spectralTerm F rho.1‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' m : Nat, ‖∑' rho : spectralHeightShell (m + N),
        spectralTerm F rho.1‖ := norm_tsum_le_tsum_norm htailTerms.norm
    _ ≤ ∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        ‖spectralTerm F rho.1‖ :=
      htailTerms.norm.tsum_le_tsum hinner htailNorms

/-- A controlled low-shell prefix is at most the negative analytic
multiplicity of the off-line anchor. -/
theorem spectralHeightShellPrefix_re_le_neg_xiMultiplicity_of_closedBall_control
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (N : Nat) (hrhoShell : dyadicShellIndex |rho.1.im| < N)
    (routeNodes : Finset Complex)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w)
    (hrawZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ N + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt ((convolutionIterate base n).convolution correction) w.1 = 0) :
    (∑ k ∈ Finset.range N, ∑' z : spectralHeightShell k,
      spectralTerm (selectedOwner base correction n).convolutionSquare z.1).re ≤
      -(xiMultiplicity rho : Real) := by
  have hrhoPrefix : rho ∈ spectralHeightShellPrefix N :=
    (mem_spectralHeightShellPrefix_iff N rho).mpr hrhoShell
  have hprefix :=
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_subset_finiteHeight_closedBall_control
      base correction n rho hoff hright ((2 : Real) ^ N)
      (spectralHeightShellPrefix N)
      (spectralHeightShellPrefix_subset_finiteHeightZeros N) hrhoPrefix routeNodes
      htargetValues hrawZeros
  rw [← sum_spectralHeightShellPrefix_eq_shell_prefix]
  exact hprefix

/-- The shell prefix has the same sign bound when the construction exports
selected-square zeros directly, rather than its stronger raw-zero data. -/
theorem spectralHeightShellPrefix_re_le_neg_xiMultiplicity_of_closedBall_square_zero_control
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (N : Nat) (hrhoShell : dyadicShellIndex |rho.1.im| < N)
    (routeNodes : Finset Complex)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w)
    (hsquareZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ N + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (w.1 - 1 / 2) = 0) :
    (∑ k ∈ Finset.range N, ∑' z : spectralHeightShell k,
      spectralTerm (selectedOwner base correction n).convolutionSquare z.1).re ≤
      -(xiMultiplicity rho : Real) := by
  have hrhoPrefix : rho ∈ spectralHeightShellPrefix N :=
    (mem_spectralHeightShellPrefix_iff N rho).mpr hrhoShell
  have hprefix :=
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_subset_finiteHeight_closedBall_square_zero_control
      base correction n rho hoff hright ((2 : Real) ^ N)
      (spectralHeightShellPrefix N)
      (spectralHeightShellPrefix_subset_finiteHeightZeros N) hrhoPrefix routeNodes
      htargetValues hsquareZeros
  rw [← sum_spectralHeightShellPrefix_eq_shell_prefix]
  exact hprefix

/-- A negative low-shell prefix survives in the full source-indexed spectral
sum whenever the absolute high-shell tail is strictly smaller than the anchor
multiplicity. -/
theorem spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) (N : Nat)
    (hprefix :
      (∑ k ∈ Finset.range N, ∑' z : spectralHeightShell k,
        spectralTerm F z.1).re ≤ -(xiMultiplicity rho : Real))
    (htail :
      (∑' m : Nat, ∑' z : spectralHeightShell (m + N),
        ‖spectralTerm F z.1‖) < (xiMultiplicity rho : Real)) :
    spectralWeilValue F < 0 := by
  have htailRe := spectralHeightShellTail_re_le_normTail F N
  have htailReLt :
      (∑' m : Nat, ∑' z : spectralHeightShell (m + N),
        spectralTerm F z.1).re < (xiMultiplicity rho : Real) :=
    htailRe.trans_lt htail
  unfold spectralWeilValue
  rw [← spectralHeightShellSum_eq_source_tsum F]
  rw [spectralHeightShellSum_split F N, Complex.add_re]
  linarith

/-- The fourth-order selected-square tail is the quantitative producer for
the strict tail premise in the preceding shell-prefix theorem. -/
theorem spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (T epsilon : Real) (htail : FourthOrderSpectralTail F rho.1 T epsilon)
    (n0 : Nat) (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.1.im| ≤ (2 : Real) ^ (n0 + 1))
    (hprefix :
      (∑ k ∈ Finset.range (n0 + 1), ∑' z : spectralHeightShell k,
        spectralTerm F z.1).re ≤ -(xiMultiplicity rho : Real))
    (hsmall : 4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 < (xiMultiplicity rho : Real)) :
    spectralWeilValue F < 0 := by
  have htailBound := spectralTail_norm_shellSum_le_of_fourthOrderTail
    F rho.1 T epsilon htail n0 hT hrhoHeight
  have htailBound' :
      (∑' m : Nat, ∑' z : spectralHeightShell (m + (n0 + 1)),
        ‖spectralTerm F z.1‖) ≤
        4 * epsilon ^ 2 * spectralMultiplicityConstant *
          (3 / 4 : Real) ^ n0 := by
    simpa only [Nat.add_assoc] using htailBound
  exact spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail
    F rho (n0 + 1) hprefix (htailBound'.trans_lt hsmall)

/-- The selected healthy owner has strictly negative spectral value when its
controlled low shells and fourth-order tail share the same interpolation
owner. -/
theorem selectedOwner_spectralWeilValue_neg_of_closedBall_control_and_fourthOrderTail
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (T epsilon : Real)
    (htail : FourthOrderSpectralTail
      (selectedOwner base correction n).convolutionSquare rho.1 T epsilon)
    (n0 : Nat) (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.1.im| ≤ (2 : Real) ^ (n0 + 1))
    (hrhoShell : dyadicShellIndex |rho.1.im| < n0 + 1)
    (routeNodes : Finset Complex)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w)
    (hrawZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (n0 + 1) + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt ((convolutionIterate base n).convolution correction) w.1 = 0)
    (hsmall : 4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 < (xiMultiplicity rho : Real)) :
    spectralWeilValue (selectedOwner base correction n).convolutionSquare < 0 := by
  have hprefix :=
    spectralHeightShellPrefix_re_le_neg_xiMultiplicity_of_closedBall_control
      base correction n rho hoff hright (n0 + 1) hrhoShell routeNodes
      htargetValues hrawZeros
  exact spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail
    (selectedOwner base correction n).convolutionSquare rho T epsilon htail n0 hT
    hrhoHeight hprefix hsmall

/-- The direct selected-square zero certificate is sufficient to turn the
controlled shell prefix and fourth-order tail into a negative spectral value. -/
theorem selectedOwner_spectralWeilValue_neg_of_closedBall_square_zero_control_and_fourthOrderTail
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (T epsilon : Real)
    (htail : FourthOrderSpectralTail
      (selectedOwner base correction n).convolutionSquare rho.1 T epsilon)
    (n0 : Nat) (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.1.im| ≤ (2 : Real) ^ (n0 + 1))
    (hrhoShell : dyadicShellIndex |rho.1.im| < n0 + 1)
    (routeNodes : Finset Complex)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w)
    (hsquareZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (n0 + 1) + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (w.1 - 1 / 2) = 0)
    (hsmall : 4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 < (xiMultiplicity rho : Real)) :
    spectralWeilValue (selectedOwner base correction n).convolutionSquare < 0 := by
  have hprefix :=
    spectralHeightShellPrefix_re_le_neg_xiMultiplicity_of_closedBall_square_zero_control
      base correction n rho hoff hright (n0 + 1) hrhoShell routeNodes
      htargetValues hsquareZeros
  exact spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail
    (selectedOwner base correction n).convolutionSquare rho T epsilon htail n0 hT
    hrhoHeight hprefix hsmall

/-- A construction carrying raw target values, selected-square zeros, and a
small fourth-order tail yields healthy Yoshida detector data on that same
half-density-shifted owner. -/
theorem selectedOwner_healthyDetectorData_of_closedBall_square_zero_control_and_fourthOrderTail
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (T epsilon : Real)
    (htail : FourthOrderSpectralTail
      (selectedOwner base correction n).convolutionSquare rho.1 T epsilon)
    (n0 : Nat) (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.1.im| ≤ (2 : Real) ^ (n0 + 1))
    (hrhoShell : dyadicShellIndex |rho.1.im| < n0 + 1)
    (routeNodes : Finset Complex)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w)
    (hsquareZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (n0 + 1) + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (w.1 - 1 / 2) = 0)
    (hsmall : 4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 < (xiMultiplicity rho : Real)) :
    HealthyYoshidaDetectorData rho.1 (selectedOwner base correction n).sourceTest := by
  have hhalf :
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 / 2 : Complex) = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (1 / 2 : Complex) = healthyUnscaledTargetValue rho.1
            ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho.1⟩ :=
          htargetValues ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho.1⟩
      _ = 0 := healthyUnscaledTargetValue_half rho.2 hoff
  have hone :
      laplaceAt ((convolutionIterate base n).convolution correction) 1 = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction) 1 =
          healthyUnscaledTargetValue rho.1
            ⟨1, mem_healthyUnscaledTargetNodes_one rho.1⟩ :=
          htargetValues ⟨1, mem_healthyUnscaledTargetNodes_one rho.1⟩
      _ = 0 := healthyUnscaledTargetValue_one rho.2 hoff
  have hthreeHalf :
      laplaceAt ((convolutionIterate base n).convolution correction)
          (3 / 2 : Complex) = 0 := by
    calc
      laplaceAt ((convolutionIterate base n).convolution correction)
          (3 / 2 : Complex) = healthyUnscaledTargetValue rho.1
            ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho.1⟩ :=
          htargetValues ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho.1⟩
      _ = 0 := healthyUnscaledTargetValue_threeHalf rho.2
  have hdetect :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (rho.1 + 1 / 2) ≠ 0 := by
    rw [htargetValues
      ⟨rho.1 + 1 / 2, mem_healthyUnscaledTargetNodes_detector rho.1⟩]
    exact healthyUnscaledTargetValue_detector_ne_zero rho.1 hoff
  change HealthyYoshidaDetectorData rho.1
    (halfDensityShift ((convolutionIterate base n).convolution correction))
  refine healthyDetectorData_halfDensityShift_of_raw_values_of_spectral_neg
    hhalf hone hthreeHalf ?_ ?_
  · exact (bne_iff_ne).mpr hdetect
  change spectralWeilValue (selectedOwner base correction n).convolutionSquare < 0
  exact
    selectedOwner_spectralWeilValue_neg_of_closedBall_square_zero_control_and_fourthOrderTail
      base correction n rho hoff hright T epsilon htail n0 hT hrhoHeight
      hrhoShell routeNodes htargetValues hsquareZeros hsmall

/-- The fixed-window nearby-zero construction supplies healthy detector data
for a selected source zero in the open right half of the critical strip.  The
finite interpolation radius is chosen only after the dyadic tail budget, so
the closed prefix and high-shell tail remain certificates for one selected
square owner. -/
theorem exists_healthyDetectorData_of_fixedWindows_nearbyZero_spectral_neg
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (routeNodes : Finset Complex)
    {baseLower baseUpper lower upper : Real}
    (hbaseLower : baseLower < 0) (hbaseUpper : 0 < baseUpper)
    (hlower : lower < 0) (hupper : 0 < upper)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho.1 g := by
  obtain ⟨base, T, _hbaseSupport, _hT, hconstruction⟩ :=
    exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets
      rho.1 rho.2 hoff routeNodes hbaseLower hbaseUpper hlower hupper epsilon hepsilon
  obtain ⟨n0, hT, hrhoHeight, hsmall⟩ :=
    exists_dyadic_tail_start_with_budget_lt_xiMultiplicity T epsilon rho
  let R : Real := (2 : Real) ^ (n0 + 1) + 2 + dist (2 : Complex) rho.1
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  obtain ⟨correction, _C, n, _hcorrectionSupport, _hselectedSupport,
      htargetValues, _hminimal, _horbitSum, hsquareZeros, _hC,
      _hcenteredTail, hsquareTail⟩ :=
    hconstruction R hR
  have himLt : |rho.1.im| < (2 : Real) ^ (n0 + 1) := by
    have hpow : 0 < (2 : Real) ^ (n0 + 1) := by positivity
    have himNonneg : 0 ≤ |rho.1.im| := abs_nonneg _
    nlinarith
  have hrhoShell : dyadicShellIndex |rho.1.im| < n0 + 1 := by
    have hminimal := Nat.find_min'
      (exists_lt_two_pow_succ |rho.1.im|) himLt
    rw [← dyadicShellIndex] at hminimal
    omega
  have hsquareZeros' :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (n0 + 1) + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (w.1 - 1 / 2) = 0 := by
    simpa only [R] using hsquareZeros
  exact ⟨(selectedOwner base correction n).sourceTest,
    selectedOwner_healthyDetectorData_of_closedBall_square_zero_control_and_fourthOrderTail
      base correction n rho hoff hright T epsilon hsquareTail n0 hT hrhoHeight
      hrhoShell routeNodes htargetValues hsquareZeros' hsmall⟩

/-- A concrete fixed-window form of the nearby-zero construction.  The
window endpoints and tail accuracy are harmless construction parameters, so
the public conclusion contains only the healthy detector data. -/
theorem exists_healthyDetectorData_of_sourceNontrivialZero_right
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho.1 g := by
  exact exists_healthyDetectorData_of_fixedWindows_nearbyZero_spectral_neg
    rho hoff hright ∅
    (baseLower := -(1 : Real)) (baseUpper := 1)
    (lower := -(1 : Real)) (upper := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (1 : Real) (by norm_num)

/-- Right-oriented detector data is enough for the spectral-sign RH exit.
Any hypothetical off-line source zero has a functional-equation representative
strictly to the right of the critical line, where the detector's strictly
negative square contradicts the assumed global spectral nonnegativity.  This
does not transport a detector from that representative back to the original
left-side zero. -/
theorem healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg
    (hdetector : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho.1 g)
    (hsign : ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g →
        0 ≤ spectralWeilValue g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH := by
  intro rho hrho
  by_cases hline : rho.re = 1 / 2
  · simpa [RHDefinitionBridge.standard] using hline
  · obtain ⟨sigma, hright, _hmultiplicity, _hchoice⟩ :=
      exists_rightOfCriticalXiZero_of_re_ne_half ⟨rho, hrho⟩ hline
    obtain ⟨g, hg⟩ := hdetector sigma hright
    have hnonneg : 0 ≤ spectralWeilValue g.convolutionSquare :=
      hsign g hg.vanishesOnF
    have hnegative : spectralWeilValue g.convolutionSquare < 0 :=
      (weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
        hg.weilSquareSumPositive
    exact False.elim ((not_lt_of_ge hnonneg) hnegative)

/-- The minimal B5-shaped exit: for each hypothetical right-hand off-line zero,
it is enough to exhibit one healthy detector whose same-owner Weil value is
nonnegative.  The detector package supplies strict negativity for that same
test, so no all-test positivity hypothesis is needed. -/
theorem healthy_sourceRH_of_right_detector_specific_qw_nonneg
    (hsemiLocal : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            0 ≤ C1SameOwnerWeil.qw g) :
    RHDefinitionBridge.standard.SourceRH := by
  intro rho hrho
  by_cases hline : rho.re = 1 / 2
  · simpa [RHDefinitionBridge.standard] using hline
  · obtain ⟨sigma, hright, _hmultiplicity, _hchoice⟩ :=
      exists_rightOfCriticalXiZero_of_re_ne_half ⟨rho, hrho⟩ hline
    obtain ⟨g, hg, hnonnegative⟩ := hsemiLocal sigma hright
    have hspectralNegative : spectralWeilValue g.convolutionSquare < 0 :=
      (weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
        hg.weilSquareSumPositive
    have hqwNegative : C1SameOwnerWeil.qw g < 0 := by
      rw [C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo]
      exact hspectralNegative
    exact False.elim ((not_lt_of_ge hnonnegative) hqwNegative)

/-- The fixed-window construction discharges the right-oriented detector
premise in the preceding RH exit.  The remaining hypothesis is precisely the
global spectral nonnegativity statement; this theorem is conditional and is
not an unconditional proof of RH. -/
theorem healthy_sourceRH_of_global_spectral_nonneg
    (hsign : ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g →
        0 ≤ spectralWeilValue g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg
  · intro rho hright
    exact exists_healthyDetectorData_of_sourceNontrivialZero_right
      rho (ne_of_gt hright) hright
  · exact hsign

end

end C1HealthyYoshidaSpectralNegativity
end Source
end ConnesWeilRH
