import ConnesWeilRH.Dev.C1XiCenterTwoGammaSummedKernel

/-!
# C1XiCenterTwoGammaTailEstimate - explicit profile-integral majorant

The summed-kernel owner already provides absolute convergence.  This module
keeps the stronger source estimate visible: a profile integral has an
`n⁻²` contribution from the origin and an exponentially small contribution
past the support-radius split.  The result is still a bound, not a sign
claim; it is the quantitative interface needed by a later tail consumer.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaTailEstimate

open MeasureTheory
open Set
open Filter
open C1SameOwnerWeil
open C1XiCenterTwoGamma
open C1XiCenterTwoGammaSummedKernel
open CCM25Concrete.CompactLogConvolution
open scoped Interval Topology

noncomputable section

private theorem profile_integral_norm_le
    (F : CompactLogTest) {n : Nat} (hn : 0 < n)
    {L : Real} (hL0 : 0 ≤ L)
    (hleHead : ∀ (n : Nat) {y : Real}, 0 < y → y ≤ supportRadius F + 1 →
      ‖gammaRArchProfileTerm F n y‖ ≤
        L * y * Real.exp (-(2 * (n : Real) * y)))
    (hleTail : ∀ (n : Nat) {y : Real}, supportRadius F + 1 < y →
      ‖gammaRArchProfileTerm F n y‖ ≤
        2 * ‖F.test 0‖ * Real.exp (-((2 * (n : Real) + 1) * y))) :
    (∫ y : Real in Ioi (0 : Real),
      ‖gammaRArchProfileTerm F n y‖) ≤
      L * (((2 * (n : Real)) ^ 2)⁻¹) +
        2 * ‖F.test 0‖ *
          Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1))) := by
  have hS : 0 < supportRadius F + 1 := by
    have hR := supportRadius_nonnegative F
    linarith
  have hintval :
      (∫ y : Real in Ioi (0 : Real),
        y * Real.exp (-(2 * (n : Real) * y))) =
        (((2 * (n : Real)) ^ 2)⁻¹) := by
    have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (2 : Real)) (r := 2 * (n : Real)) (by norm_num) (by positivity)
    have hgamma' :
        (∫ y : Real in Ioi (0 : Real),
          y * Real.exp (-(2 * (n : Real) * y))) =
          (1 / (2 * (n : Real))) ^ 2 * Real.Gamma 2 := by
      simpa [show (2 : Real) - 1 = 1 by norm_num] using hgamma
    rw [hgamma']
    norm_num [Real.Gamma_nat_eq_factorial, div_eq_mul_inv]
    ring
  have hint : IntegrableOn
      (fun y : Real => y * Real.exp (-(2 * (n : Real) * y)))
      (Ioi (0 : Real)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hintval]
    positivity
  have htailval :
      (∫ y : Real in Ioi (supportRadius F + 1),
        Real.exp (-((2 * (n : Real) + 1) * y))) =
        Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1))) /
          ((2 * (n : Real) + 1)) := by
    have hval := integral_exp_mul_Ioi
      (a := -(2 * (n : Real) + 1))
      (neg_lt_zero.mpr (by positivity)) (supportRadius F + 1)
    calc
      (∫ y : Real in Ioi (supportRadius F + 1),
          Real.exp (-((2 * (n : Real) + 1) * y))) =
          -Real.exp (-(2 * (n : Real) + 1) * (supportRadius F + 1)) /
            -(2 * (n : Real) + 1) := by
              convert hval using 1 <;> ring
      _ = Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1))) /
            (2 * (n : Real) + 1) := by
              rw [neg_div_neg_eq]
              congr 2
              ring
  have hterm : IntegrableOn (fun y : Real =>
      ‖gammaRArchProfileTerm F n y‖) (Ioi (0 : Real)) :=
    (C1XiCenterTwoGamma.integrableOn_gammaRArchProfileTerm_public F n).norm
  have hdisj : Disjoint (Ioc (0 : Real) (supportRadius F + 1))
      (Ioi (supportRadius F + 1)) := by
    rw [Set.disjoint_right]
    intro x hx1 hx2
    exact (not_lt_of_ge hx2.2) hx1
  have hsubHead : Ioc (0 : Real) (supportRadius F + 1) ⊆ Ioi (0 : Real) :=
    fun y hy => mem_Ioi.mpr hy.1
  have hsubTail : Ioi (supportRadius F + 1) ⊆ Ioi (0 : Real) :=
    fun y hy => lt_trans hS hy
  have hintg : IntegrableOn
      (fun y : Real => L * (y * Real.exp (-(2 * (n : Real) * y))))
      (Ioi (0 : Real)) := hint.const_mul L
  have hexp : IntegrableOn
      (fun y : Real => Real.exp (-((2 * (n : Real) + 1) * y)))
      (Ioi (supportRadius F + 1)) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -(2 * (n : Real) + 1))
        (neg_lt_zero.mpr (by positivity)) (supportRadius F + 1))
  have hexpScaled : IntegrableOn
      (fun y : Real =>
        2 * ‖F.test 0‖ * Real.exp (-((2 * (n : Real) + 1) * y)))
      (Ioi (supportRadius F + 1)) := hexp.const_mul _
  rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
  rw [setIntegral_union hdisj measurableSet_Ioi
    (hterm.mono_set hsubHead) (hterm.mono_set hsubTail)]
  have hheadIoc :
      (∫ y : Real in Ioc (0 : Real) (supportRadius F + 1),
        ‖gammaRArchProfileTerm F n y‖) ≤
      (∫ y : Real in Ioc (0 : Real) (supportRadius F + 1),
        L * (y * Real.exp (-(2 * (n : Real) * y)))) := by
    refine integral_mono_ae (hterm.mono_set hsubHead)
      (hintg.mono_set hsubHead) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    simpa [mul_assoc] using
      hleHead n (Set.mem_Ioc.mp hy).1 (Set.mem_Ioc.mp hy).2
  have hheadExt :
      (∫ y : Real in Ioc (0 : Real) (supportRadius F + 1),
        L * (y * Real.exp (-(2 * (n : Real) * y)))) ≤
      (∫ y : Real in Ioi (0 : Real),
        L * (y * Real.exp (-(2 * (n : Real) * y)))) := by
    refine setIntegral_mono_set hintg ?_ (Filter.Eventually.of_forall hsubHead)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg hL0
      (mul_nonneg (le_of_lt hy) (Real.exp_nonneg _))
  have hheadFinal :
      (∫ y : Real in Ioc (0 : Real) (supportRadius F + 1),
        ‖gammaRArchProfileTerm F n y‖) ≤
      L * (((2 * (n : Real)) ^ 2)⁻¹) :=
    hheadIoc.trans (hheadExt.trans (by rw [integral_const_mul, hintval]))
  have htailMono :
      (∫ y : Real in Ioi (supportRadius F + 1),
        ‖gammaRArchProfileTerm F n y‖) ≤
      (∫ y : Real in Ioi (supportRadius F + 1),
        2 * ‖F.test 0‖ * Real.exp (-((2 * (n : Real) + 1) * y))) := by
    refine integral_mono_ae (hterm.mono_set hsubTail) hexpScaled ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hleTail n hy
  have htailFinal :
      (∫ y : Real in Ioi (supportRadius F + 1),
        ‖gammaRArchProfileTerm F n y‖) ≤
      2 * ‖F.test 0‖ *
        Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1))) := by
    calc
      (∫ y : Real in Ioi (supportRadius F + 1),
          ‖gammaRArchProfileTerm F n y‖) ≤
          (∫ y : Real in Ioi (supportRadius F + 1),
            2 * ‖F.test 0‖ * Real.exp (-((2 * (n : Real) + 1) * y))) :=
        htailMono
      _ = 2 * ‖F.test 0‖ *
          (∫ y : Real in Ioi (supportRadius F + 1),
            Real.exp (-((2 * (n : Real) + 1) * y))) := by
        rw [integral_const_mul]
      _ = 2 * ‖F.test 0‖ *
          (Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1))) /
            ((2 * (n : Real) + 1))) := by
        rw [htailval]
      _ ≤ 2 * ‖F.test 0‖ *
          Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1))) := by
        apply mul_le_mul_of_nonneg_left
        · have hkpos : 0 < 2 * (n : Real) + 1 := by positivity
          apply (div_le_iff₀ hkpos).2
          have hn0 : 0 ≤ (n : Real) := Nat.cast_nonneg n
          have hk : (1 : Real) ≤ 2 * (n : Real) + 1 := by nlinarith
          nlinarith [Real.exp_nonneg
            (-((2 * (n : Real) + 1) * (supportRadius F + 1)))]
        · positivity
  exact add_le_add hheadFinal htailFinal

/-- Explicit `n⁻²` plus exponential control for one profile integral. -/
theorem exists_gammaRArchProfileIntegral_norm_bound
    (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ n : Nat, 0 < n →
        ‖gammaRArchProfileIntegral F n‖ ≤
          L * (((2 * (n : Real)) ^ 2)⁻¹) +
            2 * ‖F.test 0‖ *
              Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1))) := by
  obtain ⟨L, hL0, hleHead, hleTail⟩ :=
    C1XiCenterTwoGamma.exists_gammaRArchProfile_pointwise_majorant F
  refine ⟨L, hL0, ?_⟩
  intro n hn
  change ‖∫ y : Real in Ioi (0 : Real), gammaRArchProfileTerm F n y‖ ≤ _
  exact (norm_integral_le_integral_norm (gammaRArchProfileTerm F n)).trans
    (profile_integral_norm_le F hn hL0 hleHead hleTail)

/-! ### Shifted explicit majorant

The one-profile estimate becomes useful for a finite-prefix argument only
after it is summed over the shifted indices.  The definitions below keep the
`p`-series head and geometric exponential tail in the same real-valued owner.
-/

/-- The explicit real majorant for one Gamma_R profile integral. -/
noncomputable def gammaRArchProfileIntegralMajorant
    (F : CompactLogTest) (L : Real) (n : Nat) : Real :=
  L * (((2 * (n : Real)) ^ 2)⁻¹) +
    2 * ‖F.test 0‖ *
      Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1)))

/-- The shifted `tsum` of the explicit profile majorant. -/
noncomputable def gammaRArchProfileTailMajorant
    (F : CompactLogTest) (L : Real) (N : Nat) : Real :=
  ∑' n : Nat, gammaRArchProfileIntegralMajorant F L (n + N)

private theorem summable_gammaRArchProfileIntegralMajorant
    (F : CompactLogTest) (L : Real) (N : Nat) :
    Summable (fun n : Nat =>
      gammaRArchProfileIntegralMajorant F L (n + N)) := by
  have hA : 0 < supportRadius F + 1 := by
    linarith [supportRadius_nonnegative F]
  have hpow : Summable (fun k : Nat => (((k : Real) ^ 2)⁻¹)) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have hp : Summable (fun k : Nat =>
      L * (((2 * (k : Real)) ^ 2)⁻¹)) := by
    have hscaled := hpow.mul_left (L * (4 : Real)⁻¹)
    refine hscaled.congr (fun k => ?_)
    have heq : (((2 * (k : Real)) ^ 2)⁻¹) =
        (4 : Real)⁻¹ * (((k : Real) ^ 2)⁻¹) := by
      field_simp
      ring
    rw [heq]
    ring
  have hq0 : 0 ≤ Real.exp (-(2 * (supportRadius F + 1))) :=
    Real.exp_nonneg _
  have hq1 : Real.exp (-(2 * (supportRadius F + 1))) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hgeom : Summable (fun k : Nat =>
      (Real.exp (-(2 * (supportRadius F + 1))) ^ k)) :=
    summable_geometric_of_lt_one hq0 hq1
  have hq : Summable (fun k : Nat =>
      2 * ‖F.test 0‖ *
        Real.exp (-((2 * (k : Real) + 1) * (supportRadius F + 1)))) := by
    have hscaled := hgeom.mul_left
      (2 * ‖F.test 0‖ * Real.exp (-(supportRadius F + 1)))
    refine hscaled.congr (fun k => ?_)
    have hpoweq :
        (Real.exp (-(2 * (supportRadius F + 1))) ^ k) =
          Real.exp (((k : Real)) * (-(2 * (supportRadius F + 1)))) :=
      (Real.exp_nat_mul _ _).symm
    rw [hpoweq]
    calc
      2 * ‖F.test 0‖ * Real.exp (-(supportRadius F + 1)) *
          Real.exp (((k : Real)) * (-(2 * (supportRadius F + 1)))) =
        2 * ‖F.test 0‖ *
          (Real.exp (-(supportRadius F + 1)) *
            Real.exp (((k : Real)) * (-(2 * (supportRadius F + 1))))) := by
              ring
      _ = 2 * ‖F.test 0‖ *
          Real.exp (-(supportRadius F + 1) +
            ((k : Real) * (-(2 * (supportRadius F + 1))))) := by
              rw [← Real.exp_add]
      _ = 2 * ‖F.test 0‖ *
          Real.exp (-((2 * (k : Real) + 1) * (supportRadius F + 1))) := by
              congr 2
              ring
  have hbase : Summable (fun k : Nat =>
      gammaRArchProfileIntegralMajorant F L k) := by
    simpa only [gammaRArchProfileIntegralMajorant] using hp.add hq
  simpa only [gammaRArchProfileIntegralMajorant] using
    (summable_nat_add_iff N).2 hbase

/-- A closed `O(1 / N)` plus geometric bound for the shifted Gamma_R profile
tail majorant.  The value at `N = 0` is defined but only the positive-shift
interface below is used. -/
noncomputable def gammaRArchProfileTailExplicitRate
    (F : CompactLogTest) (L : Real) (N : Nat) : Real :=
  L / (2 * (N : Real)) +
    2 * ‖F.test 0‖ *
      Real.exp (-((2 * (N : Real) + 1) * (supportRadius F + 1))) *
        (1 - Real.exp (-(2 * (supportRadius F + 1))))⁻¹

private theorem tsum_shift_inv_sq_le (N : Nat) (hN : 0 < N) :
    (∑' n : Nat, (((n + N : Nat) : Real) ^ 2)⁻¹) ≤ 2 / (N : Real) := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) ?_
  intro K
  have hsum :
      (∑ i ∈ Finset.range K, (((i + N : Nat) : Real) ^ 2)⁻¹) =
        ∑ i ∈ Finset.Ioo (N - 1) (N + K), ((i : Real) ^ 2)⁻¹ := by
    refine Finset.sum_bij (fun i _ => i + N) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Ioo]
      omega
    · intro i hi j hj heq
      exact Nat.add_right_cancel heq
    · intro j hj
      simp only [Finset.mem_Ioo] at hj
      refine ⟨j - N, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · have hNj : N ≤ j := by omega
        exact Nat.sub_add_cancel hNj
    · intro i _
      rfl
  calc
    (∑ i ∈ Finset.range K, (((i + N : Nat) : Real) ^ 2)⁻¹) =
        ∑ i ∈ Finset.Ioo (N - 1) (N + K), ((i : Real) ^ 2)⁻¹ := hsum
    _ ≤ 2 / (((N - 1 : Nat) : Real) + 1) :=
      sum_Ioo_inv_sq_le (α := Real) (N - 1) (N + K)
    _ = 2 / (N : Real) := by
      have hden : ((N - 1 : Nat) : Real) + 1 = (N : Real) := by
        norm_cast
        omega
      rw [hden]

private theorem tsum_shift_head_le (L : Real) (hL : 0 ≤ L)
    (N : Nat) (hN : 0 < N) :
    (∑' n : Nat,
      L * (((2 * ((n + N : Nat) : Real)) ^ 2)⁻¹)) ≤
        L / (2 * (N : Real)) := by
  have hbase := tsum_shift_inv_sq_le N hN
  have hscale : 0 ≤ L * (4 : Real)⁻¹ := by positivity
  calc
    (∑' n : Nat,
      L * (((2 * ((n + N : Nat) : Real)) ^ 2)⁻¹)) =
        (L * (4 : Real)⁻¹) *
          (∑' n : Nat, ((((n + N : Nat) : Real) ^ 2)⁻¹)) := by
            rw [← tsum_mul_left]
            congr 1
            funext n
            have heq : (((2 * ((n + N : Nat) : Real)) ^ 2)⁻¹) =
                (4 : Real)⁻¹ * ((((n + N : Nat) : Real) ^ 2)⁻¹) := by
              field_simp
              ring
            rw [heq]
            ring
    _ ≤ (L * (4 : Real)⁻¹) * (2 / (N : Real)) :=
      mul_le_mul_of_nonneg_left hbase hscale
    _ = L / (2 * (N : Real)) := by
      have hN0 : (N : Real) ≠ 0 := by positivity
      field_simp
      ring

private theorem summable_shift_head (L : Real) (N : Nat) :
    Summable (fun n : Nat =>
      L * (((2 * ((n + N : Nat) : Real)) ^ 2)⁻¹)) := by
  have hpow : Summable (fun k : Nat => (((k : Real) ^ 2)⁻¹)) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun n : Nat =>
      ((((n + N : Nat) : Real) ^ 2)⁻¹)) :=
    (summable_nat_add_iff N).2 hpow
  have hscaled := hshift.mul_left (L * (4 : Real)⁻¹)
  refine hscaled.congr (fun n => ?_)
  have heq : (((2 * ((n + N : Nat) : Real)) ^ 2)⁻¹) =
      (4 : Real)⁻¹ * ((((n + N : Nat) : Real) ^ 2)⁻¹) := by
    field_simp
    ring
  rw [heq]
  ring

private theorem shifted_exponential_term_eq
    (F : CompactLogTest) (N n : Nat) :
    2 * ‖F.test 0‖ *
      Real.exp (-((2 * ((n + N : Nat) : Real) + 1) *
        (supportRadius F + 1))) =
      (2 * ‖F.test 0‖ *
        Real.exp (-((2 * (N : Real) + 1) * (supportRadius F + 1)))) *
          (Real.exp (-(2 * (supportRadius F + 1))) ^ n) := by
  symm
  have hpoweq :
      (Real.exp (-(2 * (supportRadius F + 1))) ^ n) =
        Real.exp ((n : Real) * (-(2 * (supportRadius F + 1)))) :=
    (Real.exp_nat_mul _ _).symm
  rw [hpoweq]
  calc
    2 * ‖F.test 0‖ *
        Real.exp (-((2 * (N : Real) + 1) * (supportRadius F + 1))) *
          Real.exp ((n : Real) * (-(2 * (supportRadius F + 1)))) =
      2 * ‖F.test 0‖ *
        (Real.exp (-((2 * (N : Real) + 1) * (supportRadius F + 1))) *
          Real.exp ((n : Real) * (-(2 * (supportRadius F + 1))))) := by
            ring
    _ = 2 * ‖F.test 0‖ *
        Real.exp (-((2 * (N : Real) + 1) * (supportRadius F + 1)) +
          ((n : Real) * (-(2 * (supportRadius F + 1))))) := by
            rw [← Real.exp_add]
    _ = 2 * ‖F.test 0‖ *
        Real.exp (-((2 * ((n + N : Nat) : Real) + 1) *
          (supportRadius F + 1))) := by
            congr 2
            push_cast
            ring

private theorem summable_shift_exponential
    (F : CompactLogTest) (N : Nat) :
    Summable (fun n : Nat =>
      2 * ‖F.test 0‖ *
        Real.exp (-((2 * ((n + N : Nat) : Real) + 1) *
          (supportRadius F + 1)))) := by
  have hA : 0 < supportRadius F + 1 := by
    linarith [supportRadius_nonnegative F]
  have hq0 : 0 ≤ Real.exp (-(2 * (supportRadius F + 1))) :=
    Real.exp_nonneg _
  have hq1 : Real.exp (-(2 * (supportRadius F + 1))) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hgeom : Summable (fun n : Nat =>
      Real.exp (-(2 * (supportRadius F + 1))) ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  have hscaled := hgeom.mul_left
    (2 * ‖F.test 0‖ *
      Real.exp (-((2 * (N : Real) + 1) * (supportRadius F + 1))))
  refine hscaled.congr (fun n => ?_)
  exact (shifted_exponential_term_eq F N n).symm

private theorem tsum_shift_exponential_eq (F : CompactLogTest) (N : Nat) :
    (∑' n : Nat,
      2 * ‖F.test 0‖ *
        Real.exp (-((2 * ((n + N : Nat) : Real) + 1) *
          (supportRadius F + 1)))) =
      2 * ‖F.test 0‖ *
        Real.exp (-((2 * (N : Real) + 1) * (supportRadius F + 1))) *
          (1 - Real.exp (-(2 * (supportRadius F + 1))))⁻¹ := by
  have hA : 0 < supportRadius F + 1 := by
    linarith [supportRadius_nonnegative F]
  have hq0 : 0 ≤ Real.exp (-(2 * (supportRadius F + 1))) :=
    Real.exp_nonneg _
  have hq1 : Real.exp (-(2 * (supportRadius F + 1))) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith
  rw [show (fun n : Nat =>
      2 * ‖F.test 0‖ *
        Real.exp (-((2 * ((n + N : Nat) : Real) + 1) *
          (supportRadius F + 1)))) =
      (fun n : Nat =>
        (2 * ‖F.test 0‖ *
          Real.exp (-((2 * (N : Real) + 1) * (supportRadius F + 1)))) *
            (Real.exp (-(2 * (supportRadius F + 1))) ^ n)) by
      funext n
      exact shifted_exponential_term_eq F N n]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

private theorem gammaRArchProfileTailMajorant_le_explicit_rate
    (F : CompactLogTest) (L : Real) (hL : 0 ≤ L)
    (N : Nat) (hN : 0 < N) :
    gammaRArchProfileTailMajorant F L N ≤
      gammaRArchProfileTailExplicitRate F L N := by
  unfold gammaRArchProfileTailMajorant gammaRArchProfileIntegralMajorant
    gammaRArchProfileTailExplicitRate
  rw [Summable.tsum_add (summable_shift_head L N)
    (summable_shift_exponential F N)]
  apply add_le_add
  · exact tsum_shift_head_le L hL N hN
  · rw [tsum_shift_exponential_eq F N]

/-- The shifted absolute profile tail is bounded by a summable explicit
majorant.  This is a magnitude estimate only; it makes no sign assertion
about the coupled finite Gamma_R kernel. -/
theorem gammaRArchProfileTailNorm_le_explicit_majorant
    (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ N : Nat, 0 < N →
        gammaRArchProfileTailNorm F N ≤
          gammaRArchProfileTailMajorant F L N := by
  obtain ⟨L, hL, hbound⟩ :=
    exists_gammaRArchProfileIntegral_norm_bound F
  refine ⟨L, hL, ?_⟩
  intro N hN
  have hnorm : Summable (fun n : Nat =>
      ‖gammaRArchProfileIntegral F n‖) := by
    have hcomplex : Summable (fun n : Nat =>
        gammaRArchProfileIntegral F n) := by
      have hmajor := summable_integralOn_norm_gammaRArchProfileTerm F
      apply hmajor.of_norm_bounded
      intro n
      exact norm_integral_le_integral_norm _
    exact hcomplex.norm
  have hnormShift : Summable (fun n : Nat =>
      ‖gammaRArchProfileIntegral F (n + N)‖) :=
    (summable_nat_add_iff N).2 hnorm
  have hmajorShift : Summable (fun n : Nat =>
      gammaRArchProfileIntegralMajorant F L (n + N)) :=
    summable_gammaRArchProfileIntegralMajorant F L N
  change (∑' n : Nat, ‖gammaRArchProfileIntegral F (n + N)‖) ≤
    ∑' n : Nat, gammaRArchProfileIntegralMajorant F L (n + N)
  exact hnormShift.tsum_le_tsum
    (fun n => hbound (n + N) (by omega)) hmajorShift

/-! ### Explicit pointwise certificate consumer

The existential theorem above is useful for convergence, but it hides the
constant that a finite-prefix sign proof must budget against.  This consumer
keeps the pointwise head and support-tail certificates explicit, so a later
owner can supply a constant with a meaningful normalization (for example,
one proportional to a convolution-square mass).
-/

/-- A supplied pointwise profile certificate gives the corresponding explicit
shifted tail rate.  This theorem makes no claim that the certificate constant
is universal or mass-relative. -/
theorem gammaRArchProfileTailNorm_le_explicit_rate_of_pointwise_majorant
    (F : CompactLogTest) (L : Real) (hL : 0 ≤ L)
    (hhead :
      ∀ (n : Nat) {y : Real}, 0 < y → y ≤ supportRadius F + 1 →
        ‖gammaRArchProfileTerm F n y‖ ≤
          L * y * Real.exp (-(2 * (n : Real) * y)))
    (htail :
      ∀ (n : Nat) {y : Real}, supportRadius F + 1 < y →
        ‖gammaRArchProfileTerm F n y‖ ≤
          2 * ‖F.test 0‖ *
            Real.exp (-((2 * (n : Real) + 1) * y)))
    (N : Nat) (hN : 0 < N) :
    gammaRArchProfileTailNorm F N ≤
      gammaRArchProfileTailExplicitRate F L N := by
  have hbound : ∀ n : Nat, 0 < n →
      ‖gammaRArchProfileIntegral F n‖ ≤
        gammaRArchProfileIntegralMajorant F L n := by
    intro n hn
    change ‖∫ y : Real in Ioi (0 : Real),
      gammaRArchProfileTerm F n y‖ ≤
      L * (((2 * (n : Real)) ^ 2)⁻¹) +
        2 * ‖F.test 0‖ *
          Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1)))
    exact (norm_integral_le_integral_norm _).trans
      (profile_integral_norm_le F hn hL hhead htail)
  have hnorm : Summable (fun n : Nat =>
      ‖gammaRArchProfileIntegral F n‖) := by
    have hcomplex : Summable (fun n : Nat =>
        gammaRArchProfileIntegral F n) := by
      have hmajor := summable_integralOn_norm_gammaRArchProfileTerm F
      apply hmajor.of_norm_bounded
      intro n
      exact norm_integral_le_integral_norm _
    exact hcomplex.norm
  have hnormShift : Summable (fun n : Nat =>
      ‖gammaRArchProfileIntegral F (n + N)‖) :=
    (summable_nat_add_iff N).2 hnorm
  have hmajorShift : Summable (fun n : Nat =>
      gammaRArchProfileIntegralMajorant F L (n + N)) :=
    summable_gammaRArchProfileIntegralMajorant F L N
  have hmajor : gammaRArchProfileTailNorm F N ≤
      gammaRArchProfileTailMajorant F L N := by
    change (∑' n : Nat,
      ‖gammaRArchProfileIntegral F (n + N)‖) ≤
      ∑' n : Nat,
        gammaRArchProfileIntegralMajorant F L (n + N)
    exact hnormShift.tsum_le_tsum
      (fun n => hbound (n + N) (by omega)) hmajorShift
  exact hmajor.trans
    (gammaRArchProfileTailMajorant_le_explicit_rate F L hL N hN)

/-- The shifted absolute Gamma_R profile tail has a closed `O(1 / N)` plus
geometric magnitude bound.  This is still a magnitude estimate only: it does
not assert a sign for the tail or for the full archimedean form. -/
theorem gammaRArchProfileTailNorm_le_explicit_rate
    (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ N : Nat, 0 < N →
        gammaRArchProfileTailNorm F N ≤
          gammaRArchProfileTailExplicitRate F L N := by
  obtain ⟨L, hL, hmajor⟩ := gammaRArchProfileTailNorm_le_explicit_majorant F
  refine ⟨L, hL, ?_⟩
  intro N hN
  exact (hmajor N hN).trans
    (gammaRArchProfileTailMajorant_le_explicit_rate F L hL N hN)

end
end C1XiCenterTwoGammaTailEstimate
end Source
end ConnesWeilRH
