import ConnesWeilRH.Dev.C1XiGlobalWeightedZeroSum
import ConnesWeilRH.Dev.C1XiLocalPrincipalPart

/-!
# C1XiRemovablePole - the H-A2 local cancellation layer

This module removes one source-indexed xi zero from the multiplicity-weighted
regularized sum.  The deleted sum is then treated on a ball where the selected
zero is the only xi zero.  The local factor and the deleted sum remain separate
owners until the final punctured identity is assembled.

No global Hadamard product, growth estimate, explicit formula, or RH claim is
introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiRemovablePole

open Filter
open scoped BigOperators
open C1XiGlobalZeroSum
open C1XiGlobalWeightedZeroSum
open C1XiVerticalFunctional
open C1SpectralSummability
open C1XiLocalPrincipalPart
open CC20ZetaCounting
open CC20YoshidaNearZeros
open C1SpectralWeil
open scoped Topology

noncomputable section

/-- The multiplicity-weighted regularized sum with one source zero removed.
The index is a subtype, so the exclusion is part of the summation owner. -/
noncomputable def weightedRegularizedZeroSumWithout
    (rho0 : sourceNontrivialZeroSet) (s : Complex) : Complex :=
  ∑' rho : {rho : sourceNontrivialZeroSet //
      rho ∉ ({rho0} : Finset sourceNontrivialZeroSet)},
    weightedRegularizedZeroTerm s rho.1

/-- Removing one term from the source-indexed unconditional sum. -/
theorem weightedRegularizedZeroSum_eq_selected_add_without
    (rho0 : sourceNontrivialZeroSet) (s : Complex) :
    weightedRegularizedZeroSum s =
      weightedRegularizedZeroTerm s rho0 +
        weightedRegularizedZeroSumWithout rho0 s := by
  rw [weightedRegularizedZeroSum_eq_source_tsum]
  have hsplit :=
    (weightedRegularizedZeroSummable s).sum_add_tsum_subtype_compl
      ({rho0} : Finset sourceNontrivialZeroSet)
  simpa [weightedRegularizedZeroSumWithout, Set.mem_singleton_iff] using hsplit.symm

/-- The selected source zero is isolated in a ball.  This is extracted from
the same local cofactor that supplies the principal-part identity; no global
zero-spacing assertion is used. -/
theorem exists_sourceZero_isolating_ball (rho : sourceNontrivialZeroSet) :
    ∃ r > 0, ∀ z ∈ Metric.ball rho.1 r,
      completedRiemannXi z = 0 ↔ z = rho.1 := by
  obtain ⟨h, hanalytic, hnonzero, hfactor⟩ :=
    exists_completedRiemannXi_local_factor rho
  have hne : ∀ᶠ z in 𝓝 rho.1, h z ≠ 0 :=
    (hanalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hnonzero
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hne.and hfactor)
  refine ⟨r, hr, ?_⟩
  intro z hz
  constructor
  · intro hzero
    have hzdata := hball z hz
    have hzne : h z ≠ 0 := hzdata.1
    have hzfactor : completedRiemannXi z =
        (z - rho.1) ^ xiMultiplicity rho * h z := hzdata.2
    have hprod : (z - rho.1) ^ xiMultiplicity rho * h z = 0 := by
      rw [← hzfactor]
      exact hzero
    have hpow : (z - rho.1) ^ xiMultiplicity rho = 0 :=
      (mul_eq_zero.mp hprod).resolve_right hzne
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
  · intro hz
    rw [hz]
    exact completedRiemannXi_eq_zero_of_mem_sourceNontrivialZeroSet

/-! ### H-A2: remove one selected zero from the weighted sum

The full weighted sum is not differentiable at a xi zero because its selected
summand has the matching pole.  We split at the selected zero's shell, remove
that one term from the finite prefix, and keep the shifted tail unchanged.
The tail is controlled on a small horizontal strip; no zero-free assertion is
used for the selected point itself.
-/

/-- The source-indexed weighted sum with one selected zero deleted is
differentiable at that zero. -/
theorem weightedRegularizedZeroSumWithout_hasDerivAt
    (rho0 : sourceNontrivialZeroSet) :
    ∃ D : Complex,
      HasDerivAt (weightedRegularizedZeroSumWithout rho0) D rho0.1 := by
  classical
  let m0 : Nat := dyadicShellIndex |rho0.1.im|
  have hm0 : rho0 ∈ spectralHeightShell m0 := by
    rfl
  let n0 : Nat := m0 + 1
  have hs_lt0 : |rho0.1.im| < (2 : Real) ^ n0 := by
    dsimp only [n0, m0]
    exact lt_two_pow_succ_dyadicShellIndex |rho0.1.im|
  have hgap : 0 < (2 : Real) ^ n0 - |rho0.1.im| := by
    nlinarith [hs_lt0]
  let r : Real := ((2 : Real) ^ n0 - |rho0.1.im|) / 2
  have hr : 0 < r := by
    dsimp only [r]
    exact div_pos hgap (by norm_num)
  have hy_im (y : Complex) (hy : y ∈ Metric.ball rho0.1 r) :
      |y.im| < (2 : Real) ^ n0 := by
    have hyt : ‖y - rho0.1‖ < r := by
      rw [Metric.mem_ball] at hy
      simpa [dist_eq_norm] using hy
    have him : |y.im - rho0.1.im| <= ‖y - rho0.1‖ := by
      simpa using (Complex.abs_im_le_norm (y - rho0.1))
    have htri : |y.im| <= |rho0.1.im| + r := by
      calc
        |y.im| = |rho0.1.im + (y.im - rho0.1.im)| := by
          congr 1
          ring
        _ <= |rho0.1.im| + |y.im - rho0.1.im| := abs_add_le _ _
        _ <= |rho0.1.im| + r := by nlinarith [him, hyt.le]
    dsimp only [r] at htri
    nlinarith [htri, hs_lt0]
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
      (∑' rho : spectralHeightShell (k + 1),
        (xiMultiplicity rho.1 : Real)) <=
        spectralMultiplicityConstant * 3 ^ k := by
    simpa [spectralHeightMultiplicity] using
      spectralHeightMultiplicity_geometric_bound k
  have hne_tail (m : Nat) (y : Complex)
      (hy : y ∈ Metric.ball rho0.1 r)
      (rho : spectralHeightShell (m + n0 + 1)) :
      y - rho.1 ≠ 0 := by
    intro hzero
    have him : (2 : Real) ^ (m + n0 + 1) <= |rho.1.1.im| :=
      shell_lower_im (rho := rho.1) rho.2
    have hpow : (2 : Real) ^ n0 <= (2 : Real) ^ (m + n0 + 1) := by
      apply pow_le_pow_right₀ (by norm_num : (1 : Real) <= 2)
      omega
    have hy_eq : y = rho.1 := sub_eq_zero.mp hzero
    have hgeq : (2 : Real) ^ n0 <= |y.im| := by
      calc
        (2 : Real) ^ n0 <= (2 : Real) ^ (m + n0 + 1) := hpow
        _ <= |rho.1.1.im| := him
        _ = |y.im| := by simpa [hy_eq]
    nlinarith [hy_im y hy, hgeq]
  have hg : ∀ m y, y ∈ Metric.ball rho0.1 r →
      HasDerivAt (g m) (g' m y) y := by
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
      exact weightedRegularizedZeroTerm_hasDerivAt
        (hne_tail m y hy rho)
    simpa only [tsum_fintype] using hsum
  have hg' : ∀ m y, y ∈ Metric.ball rho0.1 r → ‖g' m y‖ <= u m := by
    intro m y hy
    dsimp [g', u]
    letI := (spectralHeightShell_finite (m + n0 + 1)).fintype
    have hbound : (∑ rho : spectralHeightShell (m + n0 + 1),
        ‖weightedRegularizedZeroDeriv y rho.1‖) <=
        (∑ rho : spectralHeightShell (m + n0 + 1),
          (xiMultiplicity rho.1 : Real)) /
          ((2 : Real) ^ (m + n0)) ^ 2 := by
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
          (xiMultiplicity rho.1 : Real)) /
          ((2 : Real) ^ (m + n0)) ^ 2 := hbound
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
              have hfour :
                  (2 : Real) ^ (m + n0) * (2 : Real) ^ (m + n0) =
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
                div_le_div_of_nonneg_right hmassN_current (sq_nonneg _)
              _ = spectralMultiplicityConstant * (3 / 4 : Real) ^
                  (m + n0) := hpow
  have hg0 : Summable fun m => g m rho0.1 := by
    dsimp [g]
    exact (summable_nat_add_iff
      (f := fun k : Nat => ∑' rho : spectralHeightShell k,
        weightedRegularizedZeroTerm rho0.1 rho.1) (n0 + 1)).mpr
      (weightedRegularizedZeroShellSummable rho0.1)
  have htail : HasDerivAt (fun z : Complex => ∑' m : Nat, g m z)
      (∑' m : Nat, g' m rho0.1) rho0.1 := by
    exact hasDerivAt_tsum_of_isPreconnected hu (Metric.isOpen_ball)
      (Metric.isPreconnected_ball) hg hg' (Metric.mem_ball_self hr) hg0
      (Metric.mem_ball_self hr)
  let rho0Shell : spectralHeightShell m0 := ⟨rho0, hm0⟩
  letI := (spectralHeightShell_finite m0).fintype
  let outer : Finset Nat := (Finset.range (n0 + 1)).erase m0
  let inner0 : Complex -> Complex := fun s =>
    ∑ rho ∈ (Finset.univ.erase rho0Shell),
      weightedRegularizedZeroTerm s rho.1
  have hinner (m : Nat) (hm : m ≠ m0) :
      HasDerivAt (fun s : Complex =>
        ∑' rho : spectralHeightShell m,
          weightedRegularizedZeroTerm s rho.1)
        (∑' rho : spectralHeightShell m,
          weightedRegularizedZeroDeriv rho0.1 rho.1) rho0.1 := by
    letI := (spectralHeightShell_finite m).fintype
    have hsum : HasDerivAt (fun s : Complex =>
        ∑ rho : spectralHeightShell m,
          weightedRegularizedZeroTerm s rho.1)
        (∑ rho : spectralHeightShell m,
          weightedRegularizedZeroDeriv rho0.1 rho.1) rho0.1 := by
      refine HasDerivAt.fun_sum ?_
      intro rho hrho
      have hne : rho0.1 - rho.1.1 ≠ 0 := by
        apply sub_ne_zero.mpr
        intro heq
        have hsource : rho.1 = rho0 := Subtype.ext heq.symm
        have hmem : rho0 ∈ spectralHeightShell m := by
          simpa [hsource] using rho.property
        have hindex : m = m0 :=
          (spectralHeightShell_partition rho0).unique hmem hm0
        exact hm hindex
      exact weightedRegularizedZeroTerm_hasDerivAt hne
    simpa only [tsum_fintype] using hsum
  have hinner0 : HasDerivAt inner0
      (∑ rho ∈ (Finset.univ.erase rho0Shell),
        weightedRegularizedZeroDeriv rho0.1 rho.1) rho0.1 := by
    dsimp [inner0]
    refine HasDerivAt.fun_sum ?_
    intro rho hrho
    have hnot : rho ≠ rho0Shell := (Finset.mem_erase.mp hrho).1
    have hne : rho0.1 - rho.1.1 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      apply hnot
      apply Subtype.ext
      apply Subtype.ext
      exact heq.symm
    exact weightedRegularizedZeroTerm_hasDerivAt hne
  have houter : HasDerivAt
      (fun s : Complex =>
        ∑ m ∈ outer, ∑' rho : spectralHeightShell m,
          weightedRegularizedZeroTerm s rho.1)
      (∑ m ∈ outer, ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroDeriv rho0.1 rho.1) rho0.1 := by
    dsimp [outer]
    refine HasDerivAt.fun_sum ?_
    intro m hm
    exact hinner m (Finset.mem_erase.mp hm).1
  let prefixWithout : Complex -> Complex := fun s =>
    (∑ m ∈ outer, ∑' rho : spectralHeightShell m,
      weightedRegularizedZeroTerm s rho.1) + inner0 s
  have hprefix : HasDerivAt prefixWithout
      ((∑ m ∈ outer, ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroDeriv rho0.1 rho.1) +
        (∑ rho ∈ (Finset.univ.erase rho0Shell),
          weightedRegularizedZeroDeriv rho0.1 rho.1)) rho0.1 := by
    dsimp [prefixWithout]
    exact houter.add hinner0
  have hinner0_eq (s : Complex) :
      (∑' rho : spectralHeightShell m0,
        weightedRegularizedZeroTerm s rho.1) =
      weightedRegularizedZeroTerm s rho0 + inner0 s := by
    rw [tsum_fintype]
    have hsum := Finset.sum_erase_add
      (s := (Finset.univ : Finset (spectralHeightShell m0)))
      (f := fun rho => weightedRegularizedZeroTerm s rho.1)
      (a := rho0Shell) (Finset.mem_univ rho0Shell)
    simpa [inner0, rho0Shell, add_comm] using hsum.symm
  have houter_eq (s : Complex) :
      (∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm s rho.1) =
      (∑' rho : spectralHeightShell m0,
        weightedRegularizedZeroTerm s rho.1) +
      (∑ m ∈ outer, ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm s rho.1) := by
    have hsum := Finset.sum_erase_add
      (s := Finset.range (n0 + 1))
      (f := fun m => ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm s rho.1)
      (a := m0) (Finset.mem_range.mpr (by omega))
    simpa [outer, add_comm] using hsum.symm
  have hprefix_eq (s : Complex) :
      (∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
        weightedRegularizedZeroTerm s rho.1) =
      weightedRegularizedZeroTerm s rho0 + prefixWithout s := by
    rw [houter_eq s, hinner0_eq s]
    simp only [prefixWithout]
    ring
  have hdecomp (s : Complex) :
      weightedRegularizedZeroSumWithout rho0 s =
        prefixWithout s + (∑' m : Nat, ∑' rho : spectralHeightShell
          (m + n0 + 1), weightedRegularizedZeroTerm s rho.1) := by
    calc
      weightedRegularizedZeroSumWithout rho0 s =
          weightedRegularizedZeroSum s - weightedRegularizedZeroTerm s rho0 := by
            rw [weightedRegularizedZeroSum_eq_selected_add_without rho0 s]
            ring
      _ = ((∑ m ∈ Finset.range (n0 + 1), ∑' rho : spectralHeightShell m,
          weightedRegularizedZeroTerm s rho.1) +
          (∑' m : Nat, ∑' rho : spectralHeightShell (m + n0 + 1),
            weightedRegularizedZeroTerm s rho.1)) -
          weightedRegularizedZeroTerm s rho0 := by
            rw [weightedRegularizedZeroSum]
            rw [weightedRegularizedZeroSum_split_shell s (n0 + 1)]
            have htail_eq :
                (∑' m : Nat, ∑' rho : spectralHeightShell (m + (n0 + 1)),
                  weightedRegularizedZeroTerm s rho.1) =
                (∑' m : Nat, ∑' rho : spectralHeightShell (m + n0 + 1),
                  weightedRegularizedZeroTerm s rho.1) := by
              apply tsum_congr
              intro m
              have hindex : m + (n0 + 1) = m + n0 + 1 := by omega
              rw [hindex]
            rw [htail_eq]
      _ = prefixWithout s + (∑' m : Nat, ∑' rho : spectralHeightShell
          (m + n0 + 1), weightedRegularizedZeroTerm s rho.1) := by
            rw [hprefix_eq s]
            ring
  let D : Complex :=
    (∑ m ∈ outer, ∑' rho : spectralHeightShell m,
      weightedRegularizedZeroDeriv rho0.1 rho.1) +
      (∑ rho ∈ (Finset.univ.erase rho0Shell),
        weightedRegularizedZeroDeriv rho0.1 rho.1) +
      (∑' m : Nat, g' m rho0.1)
  refine ⟨D, ?_⟩
  have hmain : HasDerivAt
      (fun s : Complex => prefixWithout s + ∑' m : Nat, g m s) D rho0.1 := by
    simpa [D, g] using hprefix.add htail
  have heq : (fun s : Complex => weightedRegularizedZeroSumWithout rho0 s) =ᶠ[
      𝓝 rho0.1] (fun s : Complex => prefixWithout s + ∑' m : Nat, g m s) := by
    filter_upwards [] with s
    simpa [g] using hdecomp s
  exact hmain.congr_of_eventuallyEq heq

/-- The deleted weighted sum is holomorphic on a sufficiently small ball
around the selected zero.  At the center this is H-A2's finite-prefix/tail
argument; at every other point in the isolating ball, H-A1 applies to the
full sum and the selected summand is an ordinary holomorphic term. -/
theorem weightedRegularizedZeroSumWithout_analyticOn_ball
    (rho0 : sourceNontrivialZeroSet) :
    ∃ r > 0,
      AnalyticOnNhd Complex (weightedRegularizedZeroSumWithout rho0)
        (Metric.ball rho0.1 r) := by
  obtain ⟨r, hr, hiso⟩ := exists_sourceZero_isolating_ball rho0
  have hdiff : DifferentiableOn Complex
      (weightedRegularizedZeroSumWithout rho0) (Metric.ball rho0.1 r) := by
    intro z hz
    by_cases hz0 : z = rho0.1
    · subst z
      obtain ⟨D, hD⟩ := weightedRegularizedZeroSumWithout_hasDerivAt rho0
      exact hD.differentiableAt.differentiableWithinAt
    · have hxi : completedRiemannXi z ≠ 0 := by
        intro hzero
        exact hz0 ((hiso z hz).mp hzero)
      obtain ⟨Dfull, hfull⟩ :=
        weightedRegularizedZeroSum_hasDerivAt z hxi
      have hterm := weightedRegularizedZeroTerm_hasDerivAt
        (sub_ne_zero.mpr hz0)
      have hsub := hfull.sub hterm
      have heq : (fun w : Complex =>
          weightedRegularizedZeroSumWithout rho0 w) =ᶠ[𝓝 z]
          (fun w : Complex =>
            weightedRegularizedZeroSum w -
              weightedRegularizedZeroTerm w rho0) := by
        filter_upwards [] with w
        rw [weightedRegularizedZeroSum_eq_selected_add_without rho0 w]
        ring
      exact hsub.congr_of_eventuallyEq heq |>.differentiableAt.differentiableWithinAt
  exact ⟨r, hr, hdiff.analyticOnNhd Metric.isOpen_ball⟩

/-! ### H-A2 local factor assembly

The local factor theorem below records the sign-correct cancellation for the
positive logarithmic derivative.  The companion negative logarithmic
derivative identity is obtained by negating this equation; it is not a second
independent pole convention.
-/

/-- One local cofactor makes the difference between `logDeriv xi` and the
weighted regularized zero sum analytic across the selected zero. -/
theorem exists_local_xiLogDeriv_weightedDifference
    (rho : sourceNontrivialZeroSet) :
    ∃ h H : Complex -> Complex, ∃ r > 0,
      AnalyticAt Complex h rho.1 ∧ h rho.1 ≠ 0 ∧
      AnalyticOnNhd Complex H (Metric.ball rho.1 r) ∧
      (∀ᶠ s in 𝓝[≠] rho.1,
        logDeriv completedRiemannXi s - weightedRegularizedZeroSum s = H s) ∧
      (∀ s ∈ Metric.ball rho.1 r,
        H s = logDeriv h s - (xiMultiplicity rho : Complex) / rho.1 -
          weightedRegularizedZeroSumWithout rho s) := by
  obtain ⟨h, hanalytic, hnonzero, hlocal⟩ :=
    exists_negativeXiLogDeriv_local_principal_part rho
  have hpositive : ∀ᶠ s in 𝓝[≠] rho.1,
      logDeriv completedRiemannXi s =
        (xiMultiplicity rho : Complex) / (s - rho.1) + logDeriv h s := by
    filter_upwards [hlocal] with s hs
    unfold negativeXiLogDeriv at hs
    have hneg := congrArg Neg.neg hs
    convert hneg using 1 <;> ring
  obtain ⟨Ranalytic, hRanalytic, hanalyticOn⟩ :=
    hanalytic.exists_ball_analyticOnNhd
  have hnonzeroEventually : ∀ᶠ s in 𝓝 rho.1, h s ≠ 0 :=
    (hanalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hnonzero
  obtain ⟨Rnonzero, hRnonzero, hnonzeroOn⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp hnonzeroEventually
  obtain ⟨Rwithout, hRwithout, hwithout⟩ :=
    weightedRegularizedZeroSumWithout_analyticOn_ball rho
  let R : Real := min Ranalytic (min Rnonzero Rwithout) / 2
  have hRmin : 0 < min Ranalytic (min Rnonzero Rwithout) :=
    lt_min hRanalytic (lt_min hRnonzero hRwithout)
  have hR : 0 < R := by
    dsimp [R]
    exact half_pos hRmin
  have hRlt : R < min Ranalytic (min Rnonzero Rwithout) := by
    dsimp [R]
    linarith
  have hRltAnalytic : R < Ranalytic :=
    hRlt.trans_le (min_le_left _ _)
  have hRleNonzero : R ≤ Rnonzero :=
    hRlt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRleWithout : R ≤ Rwithout :=
    hRlt.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hanalyticBall : AnalyticOnNhd Complex h (Metric.ball rho.1 R) :=
    hanalyticOn.mono (Metric.ball_subset_ball hRltAnalytic.le)
  have hnonzeroBall : ∀ s ∈ Metric.ball rho.1 R, h s ≠ 0 := by
    intro s hs
    apply hnonzeroOn
    rw [Metric.mem_closedBall]
    rw [Metric.mem_ball] at hs
    exact hs.le.trans hRleNonzero
  have hwithoutBall : AnalyticOnNhd Complex
      (weightedRegularizedZeroSumWithout rho) (Metric.ball rho.1 R) :=
    hwithout.mono (Metric.ball_subset_ball hRleWithout)
  have hlog : AnalyticOnNhd Complex (logDeriv h) (Metric.ball rho.1 R) := by
    intro s hs
    simpa only [logDeriv_apply] using
      (hanalyticBall s hs).deriv.div (hanalyticBall s hs) (hnonzeroBall s hs)
  let H : Complex -> Complex := fun s =>
    logDeriv h s - (xiMultiplicity rho : Complex) / rho.1 -
      weightedRegularizedZeroSumWithout rho s
  have hH : AnalyticOnNhd Complex H (Metric.ball rho.1 R) := by
    dsimp [H]
    exact (hlog.sub analyticOnNhd_const).sub hwithoutBall
  have hrho_ne : rho.1 ≠ 0 := by
    intro hz
    have hre := sourceNontrivialZero_zero_lt_re rho.2
    rw [hz] at hre
    norm_num at hre
  have hpunct : ∀ᶠ s in 𝓝[≠] rho.1,
      logDeriv completedRiemannXi s - weightedRegularizedZeroSum s = H s := by
    filter_upwards [hpositive, self_mem_nhdsWithin] with s hs hne
    have hsne : s - rho.1 ≠ 0 := by
      apply sub_ne_zero.mpr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
    have hsum := weightedRegularizedZeroSum_eq_selected_add_without rho s
    have hcast : algebraMap ℝ ℂ (xiMultiplicity rho : Real) =
        (xiMultiplicity rho : Complex) := by
      norm_num
    dsimp [H]
    rw [hsum, hs]
    unfold weightedRegularizedZeroTerm regularizedZeroTerm
    rw [hcast]
    field_simp [hrho_ne, hsne]
    ring
  refine ⟨h, H, R, hR, hanalytic, hnonzero, hH, hpunct, ?_⟩
  intro s hs
  rfl

end
end C1XiRemovablePole
end Source
end ConnesWeilRH
