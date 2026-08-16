import ConnesWeilRH.Dev.C1XiGrowth
import ConnesWeilRH.Dev.C1SpectralWeil

/-!
# C1SpectralSummability

This module closes the convergence half of Gate 2.  The theta-kernel moment
bound gives xi growth of order `exp (O(R log R))`; on dyadic Jensen circles,
`R log R` is bounded by a geometric sequence with ratio `3 < 4`.  Analytic
zero multiplicities are retained throughout and the existing quadratic
Laplace decay then makes the spectral expression absolutely summable.

No explicit-formula equality, positivity criterion, or RH statement is proved
here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralSummability

open scoped Topology BigOperators
open CC20ZetaCounting
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1XiGrowth
open C1SpectralWeil

/-- The fixed small-end Gamma contribution to the folded kernel moment. -/
noncomputable def kernelSmallMomentConstant : Real :=
  (1 / Real.pi) ^ (1 / 4 : Real) * Real.Gamma (1 / 4)

theorem kernelSmallMomentConstant_nonneg :
    0 <= kernelSmallMomentConstant := by
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.Gamma_pos_of_pos (by norm_num : (0 : Real) < 1 / 4)).le

/-- All fixed factors in the polynomial-times-kernel bound for xi. -/
noncomputable def xiGrowthFixedConstant : Real :=
  2 * completedRiemannXiKernelTailConstant *
    (kernelSmallMomentConstant + 1)

theorem xiGrowthFixedConstant_nonneg : 0 <= xiGrowthFixedConstant := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) completedRiemannXiKernelTailConstant_nonneg)
    (add_nonneg kernelSmallMomentConstant_nonneg zero_le_one)

/-- The elementary strict-threshold estimate.  Its left side is the dyadic
`R log R` scale and the right side has ratio `3`, safely below the quadratic
summability threshold `4`. -/
theorem nat_add_four_mul_two_pow_le_three_pow (n : Nat) :
    ((n : Real) + 4) * (2 : Real) ^ (n + 4) <= 64 * (3 : Real) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        (((n + 1 : Nat) : Real) + 4) * (2 : Real) ^ (n + 1 + 4) =
            (2 * ((n : Real) + 5)) * (2 : Real) ^ (n + 4) := by
              push_cast
              rw [show n + 1 + 4 = (n + 4) + 1 by omega, pow_succ]
              ring
        _ <= (3 * ((n : Real) + 4)) * (2 : Real) ^ (n + 4) := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
              linarith
        _ = 3 * (((n : Real) + 4) * (2 : Real) ^ (n + 4)) := by ring
        _ <= 3 * (64 * (3 : Real) ^ n) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 64 * (3 : Real) ^ (n + 1) := by rw [pow_succ]; ring

theorem two_pow_le_exp_nat (k : Nat) :
    (2 : Real) ^ k <= Real.exp (k : Real) := by
  have htwo : (2 : Real) <= Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  calc
    (2 : Real) ^ k <= (Real.exp 1) ^ k :=
      pow_le_pow_left₀ (by norm_num) htwo k
    _ = Real.exp (k : Real) := Real.exp_one_pow k

theorem dyadicSquare_le_exp (k : Nat) :
    ((2 : Real) ^ k) ^ 2 <= Real.exp (2 * (k : Real)) := by
  calc
    ((2 : Real) ^ k) ^ 2 = (2 : Real) ^ (k * 2) := by rw [pow_mul]
    _ <= Real.exp ((k * 2 : Nat) : Real) := two_pow_le_exp_nat (k * 2)
    _ = Real.exp (2 * (k : Real)) := by
      congr 1
      push_cast
      ring

theorem pow_self_le_exp_dyadic
    {m k : Nat} (hm : m <= 2 ^ k) :
    (m : Real) ^ m <= Real.exp ((k : Real) * (2 : Real) ^ k) := by
  have hmReal : (m : Real) <= (2 : Real) ^ k := by exact_mod_cast hm
  calc
    (m : Real) ^ m <= ((2 : Real) ^ k) ^ m :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) hmReal m
    _ = (2 : Real) ^ (k * m) := by rw [pow_mul]
    _ <= Real.exp ((k * m : Nat) : Real) := two_pow_le_exp_nat (k * m)
    _ <= Real.exp ((k : Real) * (2 : Real) ^ k) := by
      apply Real.exp_le_exp.mpr
      push_cast
      exact mul_le_mul_of_nonneg_left hmReal (Nat.cast_nonneg k)

/-- The sharp dyadic exponent inherited from the kernel-moment estimate.
At radius `R = 2^(n + 4)`, its variable part is `O(R log R)`.  The separate
geometric relaxation below exists only for spectral summability. -/
noncomputable def xiDyadicRLogRGrowthExponent (n : Nat) : Real :=
  xiGrowthFixedConstant + 1 + 2 * ((n + 4 : Nat) : Real) +
    ((n + 4 : Nat) : Real) * (2 : Real) ^ (n + 4)

/-- Uniform xi growth on the folded dyadic ball at the sharp `R log R` scale. -/
theorem norm_completedRiemannXi_le_exp_of_halfplane_dyadic_rlogr
    (n : Nat) {w : Complex} (hwRe : (1 / 2 : Real) <= w.re)
    (hwNorm : ‖w‖ <= (2 : Real) ^ (n + 4)) :
    ‖completedRiemannXi w‖ <= Real.exp (xiDyadicRLogRGrowthExponent n) := by
  let k : Nat := n + 4
  let R : Real := (2 : Real) ^ k
  let m : Nat := Nat.ceil (w.re / 2)
  have hRNonneg : 0 <= R := by simp only [R]; positivity
  have hROne : 1 <= R := by
    simp only [R]
    exact one_le_pow₀ (by norm_num)
  have hwNormR : ‖w‖ <= R := by simpa only [R, k] using hwNorm
  have hwReUpper : w.re <= R := (Complex.re_le_norm w).trans hwNormR
  have hm : m <= 2 ^ k := by
    apply Nat.ceil_le.mpr
    have hhalf : w.re / 2 <= R := by
      linarith [hwReUpper]
    simpa only [R, Nat.cast_pow, Nat.cast_ofNat] using hhalf
  have hmPos : 0 < m := by
    apply Nat.ceil_pos.mpr
    linarith
  have hmOne : (1 : Real) <= (m : Real) := by exact_mod_cast hmPos
  have hmPowOne : (1 : Real) <= (m : Real) ^ m := one_le_pow₀ hmOne
  have hmoment := completedRiemannXiKernelMoment_le hwRe
  have hmoment' :
      completedRiemannXiKernelMoment w.re <=
        completedRiemannXiKernelTailConstant *
          (kernelSmallMomentConstant + (m : Real) ^ m) := by
    simpa only [kernelSmallMomentConstant, m] using hmoment
  have hsmallLe :
      kernelSmallMomentConstant + (m : Real) ^ m <=
        (kernelSmallMomentConstant + 1) * (m : Real) ^ m := by
    have hmul : kernelSmallMomentConstant <=
        kernelSmallMomentConstant * (m : Real) ^ m := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmPowOne kernelSmallMomentConstant_nonneg
    calc
      kernelSmallMomentConstant + (m : Real) ^ m =
          (m : Real) ^ m + kernelSmallMomentConstant := by ring
      _ <= (m : Real) ^ m + kernelSmallMomentConstant * (m : Real) ^ m :=
        add_le_add_right hmul _
      _ = (kernelSmallMomentConstant + 1) * (m : Real) ^ m := by ring
  have hmomentHalf :
      completedRiemannXiKernelMoment w.re / 2 <=
        completedRiemannXiKernelTailConstant *
          (kernelSmallMomentConstant + 1) * (m : Real) ^ m := by
    have hupperNonneg : 0 <= completedRiemannXiKernelTailConstant *
        (kernelSmallMomentConstant + (m : Real) ^ m) :=
      mul_nonneg completedRiemannXiKernelTailConstant_nonneg
        (add_nonneg kernelSmallMomentConstant_nonneg (pow_nonneg (by positivity) _))
    calc
      completedRiemannXiKernelMoment w.re / 2 <=
          (completedRiemannXiKernelTailConstant *
            (kernelSmallMomentConstant + (m : Real) ^ m)) / 2 := by
              exact div_le_div_of_nonneg_right hmoment' (by norm_num)
      _ <= completedRiemannXiKernelTailConstant *
          (kernelSmallMomentConstant + (m : Real) ^ m) := by
            linarith
      _ <= completedRiemannXiKernelTailConstant *
          ((kernelSmallMomentConstant + 1) * (m : Real) ^ m) :=
            mul_le_mul_of_nonneg_left hsmallLe
              completedRiemannXiKernelTailConstant_nonneg
      _ = completedRiemannXiKernelTailConstant *
          (kernelSmallMomentConstant + 1) * (m : Real) ^ m := by ring
  have hwSub : ‖w - 1‖ <= 2 * R := by
    calc
      ‖w - 1‖ <= ‖w‖ + ‖(1 : Complex)‖ := norm_sub_le w 1
      _ = ‖w‖ + 1 := by norm_num
      _ <= R + 1 := add_le_add_left hwNormR 1
      _ <= 2 * R := by linarith
  have hmomentHalfNonneg :
      0 <= completedRiemannXiKernelMoment w.re / 2 :=
    div_nonneg (completedRiemannXiKernelMoment_nonneg w.re) (by norm_num)
  have hraw : ‖completedRiemannXi w‖ <=
      xiGrowthFixedConstant * R ^ 2 * (m : Real) ^ m + 1 := by
    calc
      ‖completedRiemannXi w‖ <=
          ‖w‖ * ‖w - 1‖ *
            (completedRiemannXiKernelMoment w.re / 2) + 1 :=
              norm_completedRiemannXi_le_kernelMoment w
      _ <= R * ‖w - 1‖ *
          (completedRiemannXiKernelMoment w.re / 2) + 1 := by
            gcongr
      _ <= R * (2 * R) *
          (completedRiemannXiKernelMoment w.re / 2) + 1 := by
            gcongr
      _ <= R * (2 * R) *
          (completedRiemannXiKernelTailConstant *
            (kernelSmallMomentConstant + 1) * (m : Real) ^ m) + 1 := by
              gcongr
      _ = xiGrowthFixedConstant * R ^ 2 * (m : Real) ^ m + 1 := by
            simp only [xiGrowthFixedConstant]
            ring
  have hfixedExp : xiGrowthFixedConstant <=
      Real.exp xiGrowthFixedConstant := by
    calc
      xiGrowthFixedConstant <= xiGrowthFixedConstant + 1 := by linarith
      _ <= Real.exp xiGrowthFixedConstant := Real.add_one_le_exp _
  have hRExp : R ^ 2 <= Real.exp (2 * (k : Real)) := by
    simpa only [R] using dyadicSquare_le_exp k
  have hmExp : (m : Real) ^ m <=
      Real.exp ((k : Real) * R) := by
    simpa only [R] using pow_self_le_exp_dyadic hm
  let E : Real := xiGrowthFixedConstant + 2 * (k : Real) + (k : Real) * R
  have hprod : xiGrowthFixedConstant * R ^ 2 * (m : Real) ^ m <=
      Real.exp E := by
    calc
      xiGrowthFixedConstant * R ^ 2 * (m : Real) ^ m <=
          Real.exp xiGrowthFixedConstant * Real.exp (2 * (k : Real)) *
            Real.exp ((k : Real) * R) := by gcongr
      _ = Real.exp E := by
        simp only [E, ← Real.exp_add]
  have hkNonneg : 0 <= (k : Real) := Nat.cast_nonneg k
  have hENonneg : 0 <= E := by
    dsimp only [E]
    exact add_nonneg
      (add_nonneg xiGrowthFixedConstant_nonneg
        (mul_nonneg (by norm_num) hkNonneg))
      (mul_nonneg hkNonneg hRNonneg)
  have htwoExp : (2 : Real) <= Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  calc
    ‖completedRiemannXi w‖ <=
        xiGrowthFixedConstant * R ^ 2 * (m : Real) ^ m + 1 := hraw
    _ <= Real.exp E + 1 := by nlinarith [hprod]
    _ <= Real.exp E + Real.exp E := by
      nlinarith [Real.one_le_exp hENonneg]
    _ = 2 * Real.exp E := by ring
    _ <= Real.exp 1 * Real.exp E :=
      mul_le_mul_of_nonneg_right htwoExp (Real.exp_pos E).le
    _ = Real.exp (E + 1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (xiDyadicRLogRGrowthExponent n) := by
      congr 1
      dsimp only [xiDyadicRLogRGrowthExponent, E, k, R]
      ring

/-- A geometric relaxation of the sharp dyadic bound.  It is retained for
the spectral summability argument, whose decay needs a ratio below `4`. -/
theorem norm_completedRiemannXi_le_exp_of_halfplane_dyadic
    (n : Nat) {w : Complex} (hwRe : (1 / 2 : Real) <= w.re)
    (hwNorm : ‖w‖ <= (2 : Real) ^ (n + 4)) :
    ‖completedRiemannXi w‖ <=
      Real.exp (xiGrowthFixedConstant + 1 + 192 * (3 : Real) ^ n) := by
  refine (norm_completedRiemannXi_le_exp_of_halfplane_dyadic_rlogr n hwRe hwNorm).trans ?_
  apply Real.exp_le_exp.mpr
  unfold xiDyadicRLogRGrowthExponent
  have hmain : ((n + 4 : Nat) : Real) * (2 : Real) ^ (n + 4) <=
      64 * (3 : Real) ^ n := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      nat_add_four_mul_two_pow_le_three_pow n
  have hpow : (1 : Real) <= (2 : Real) ^ (n + 4) :=
    one_le_pow₀ (by norm_num)
  have hk : 0 <= ((n + 4 : Nat) : Real) := Nat.cast_nonneg _
  have hlinear : ((n + 4 : Nat) : Real) <=
      ((n + 4 : Nat) : Real) * (2 : Real) ^ (n + 4) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hk
  nlinarith

/-- The preceding folded-ball estimate controls the doubled Jensen circle for
the height window `2^(n+2)`. -/
theorem norm_completedRiemannXi_le_exp_on_dyadic_jensen_sphere
    (n : Nat) {z : Complex}
    (hz : z ∈ Metric.sphere (2 : Complex)
      (2 * ((2 : Real) ^ (n + 2) + 2))) :
    ‖completedRiemannXi z‖ <=
      Real.exp (xiGrowthFixedConstant + 1 + 192 * (3 : Real) ^ n) := by
  rcases exists_half_le_re_norm_le_add_one_and_norm_completedRiemannXi_eq z with
    ⟨w, hwRe, hwNorm, hxiNorm⟩
  rw [← hxiNorm]
  apply norm_completedRiemannXi_le_exp_of_halfplane_dyadic n hwRe
  have hzDist : dist z 2 = 2 * ((2 : Real) ^ (n + 2) + 2) := by
    simpa only [Metric.mem_sphere] using hz
  have hzNorm : ‖z‖ <= 2 * ((2 : Real) ^ (n + 2) + 2) + 2 := by
    calc
      ‖z‖ = dist z 0 := (dist_zero_right z).symm
      _ <= dist z 2 + dist 2 0 := dist_triangle _ _ _
      _ = 2 * ((2 : Real) ^ (n + 2) + 2) + 2 := by
        rw [hzDist]
        norm_num
  have hpowFour : (4 : Real) <= (2 : Real) ^ (n + 2) := by
    rw [show (4 : Real) = (2 : Real) ^ 2 by norm_num]
    exact pow_right_mono₀ (by norm_num) (by omega : 2 <= n + 2)
  have hwRaw : ‖w‖ <= 2 * ((2 : Real) ^ (n + 2) + 2) + 3 :=
    hwNorm.trans (by linarith)
  calc
    ‖w‖ <= 2 * ((2 : Real) ^ (n + 2) + 2) + 3 := hwRaw
    _ <= 4 * (2 : Real) ^ (n + 2) := by linarith
    _ = (2 : Real) ^ (n + 4) := by ring_nf

/-- One explicit nonnegative Jensen constant for all dyadic windows. -/
noncomputable def spectralMultiplicityConstant : Real :=
  (xiGrowthFixedConstant + 1 +
    |Real.log ‖completedRiemannXi 2‖| + 192) / Real.log 2

theorem spectralMultiplicityConstant_nonneg :
    0 <= spectralMultiplicityConstant := by
  unfold spectralMultiplicityConstant
  exact div_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg xiGrowthFixedConstant_nonneg zero_le_one) (abs_nonneg _))
      (by norm_num))
    (Real.log_pos one_lt_two).le

theorem finiteHeightMultiplicity_dyadic_le (n : Nat) :
    (finiteHeightMultiplicity ((2 : Real) ^ (n + 2)) : Real) <=
      spectralMultiplicityConstant * (3 : Real) ^ n := by
  let G : Real := xiGrowthFixedConstant + 1 + 192 * (3 : Real) ^ n
  have hG : 0 <= G := by
    dsimp only [G]
    exact add_nonneg
      (add_nonneg xiGrowthFixedConstant_nonneg zero_le_one)
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
  have hJensen := finiteHeightMultiplicity_cast_le_of_xi_exp_sphere_bound
    (T := (2 : Real) ^ (n + 2)) (G := G)
    (by
      have hTnonneg : 0 <= (2 : Real) ^ (n + 2) := by positivity
      linarith) hG
    (by
      intro z hz
      simpa only [G] using
        norm_completedRiemannXi_le_exp_on_dyadic_jensen_sphere n hz)
  have hpowOne : (1 : Real) <= (3 : Real) ^ n := one_le_pow₀ (by norm_num)
  let fixed : Real := xiGrowthFixedConstant + 1 +
    |Real.log ‖completedRiemannXi 2‖|
  have hfixedNonneg : 0 <= fixed := by
    dsimp only [fixed]
    exact add_nonneg
      (add_nonneg xiGrowthFixedConstant_nonneg zero_le_one) (abs_nonneg _)
  have hfixedScale : fixed <= fixed * (3 : Real) ^ n := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpowOne hfixedNonneg
  have hlog : -Real.log ‖completedRiemannXi 2‖ <=
      |Real.log ‖completedRiemannXi 2‖| := neg_le_abs _
  have hnumerator : G - Real.log ‖completedRiemannXi 2‖ <=
      (xiGrowthFixedConstant + 1 +
        |Real.log ‖completedRiemannXi 2‖| + 192) * (3 : Real) ^ n := by
    dsimp only [G, fixed] at hfixedScale ⊢
    nlinarith
  calc
    (finiteHeightMultiplicity ((2 : Real) ^ (n + 2)) : Real) <=
        (G - Real.log ‖completedRiemannXi 2‖) / Real.log 2 := hJensen
    _ <= ((xiGrowthFixedConstant + 1 +
          |Real.log ‖completedRiemannXi 2‖| + 192) * (3 : Real) ^ n) /
          Real.log 2 := by
            exact div_le_div_of_nonneg_right hnumerator
              (Real.log_pos one_lt_two).le
    _ = spectralMultiplicityConstant * (3 : Real) ^ n := by
      unfold spectralMultiplicityConstant
      field_simp

theorem spectralHeightMultiplicity_geometric_bound (n : Nat) :
    spectralHeightMultiplicity (n + 1) <=
      spectralMultiplicityConstant * (3 : Real) ^ n :=
  (spectralHeightMultiplicity_le_finiteHeightMultiplicity n).trans
    (finiteHeightMultiplicity_dyadic_le n)

/-- The independently defined zero-spectral expression is absolutely
summable for every compact-log test. -/
theorem spectralSummable (F : CompactLogTest) : Summable (spectralTerm F) := by
  apply spectralSummable_of_geometric_heightMultiplicity_bound
    (K := spectralMultiplicityConstant) (q := 3) F (by norm_num) (by norm_num)
  exact spectralHeightMultiplicity_geometric_bound

theorem spectralSummableProp (F : CompactLogTest) : SpectralSummable F :=
  spectralSummable F

/-- Absolute convergence is no longer an independent Gate 2 premise.  The
remaining statement is the genuinely analytic equality between the complete
same-owner arithmetic functional and the independently defined spectral sum. -/
theorem gate2ExplicitFormula_iff (F : CompactLogTest) :
    gate2ExplicitFormula F ↔
      C1SameOwnerWeil.psi F = spectralWeilValue F := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨spectralSummableProp F, h⟩

/-- Square specialization of the reduced Gate 2 consumer.  The test passed to
both sides is definitionally the same two-fold convolution square. -/
theorem gate2ExplicitFormulaOnSquare_iff (g : CompactLogTest) :
    gate2ExplicitFormulaOnSquare g ↔
      C1SameOwnerWeil.psi g.convolutionSquare =
        spectralWeilValue g.convolutionSquare := by
  exact gate2ExplicitFormula_iff g.convolutionSquare

end C1SpectralSummability
end Source
end ConnesWeilRH
