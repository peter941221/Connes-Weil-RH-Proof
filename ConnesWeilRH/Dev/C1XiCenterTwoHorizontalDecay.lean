import ConnesWeilRH.Dev.C1XiCenterTwoHorizontal

/-!
# C1XiCenterTwoHorizontalDecay - explicit dyadic decay

The center-`2` Borel estimate gives a cofactor logarithmic-derivative budget,
and the zero-free tubes give a finite-principal-part budget.  This module
reduces their sum to a geometric majorant with base `12`.  The fourth power
of the selected dyadic height has base `16`, so the normalized envelope tends
to zero.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoHorizontalDecay

open Set
open Filter
open CC20ZetaCounting
open C1SpectralSummability
open C1XiQuantitativeHeight
open C1XiQuantitativePrincipalBound
open C1XiCofactorBorel
open C1XiCenterTwoHorizontal
open scoped Topology

noncomputable section

/-- Fixed coefficient absorbing the relaxed dyadic xi exponent and the
normalization value at `2`. -/
noncomputable def dyadicCofactorFixedGrowthCoefficient : Real :=
  xiGrowthFixedConstant + 1 + 192 +
    |Real.log ‖completedRiemannXi 2‖|

/-- Fixed logarithmic coefficient for the factor radius and radial-grid
penalty. -/
noncomputable def dyadicCofactorLogGrowthCoefficient : Real :=
  Real.log 2 +
    |Real.log (4 * (spectralMultiplicityConstant + 2))| +
    Real.log 3

/-- One global coefficient for the same-owner horizontal xi envelope. -/
noncomputable def dyadicCenterTwoTotalGrowthConstant : Real :=
  64 * dyadicCofactorFixedGrowthCoefficient +
    9216 * spectralMultiplicityConstant *
      dyadicCofactorLogGrowthCoefficient +
    108 * spectralMultiplicityConstant ^ 2 +
    72 * spectralMultiplicityConstant

theorem dyadicCofactorFixedGrowthCoefficient_nonneg :
    0 ≤ dyadicCofactorFixedGrowthCoefficient := by
  unfold dyadicCofactorFixedGrowthCoefficient
  exact add_nonneg
    (add_nonneg
      (add_nonneg xiGrowthFixedConstant_nonneg (by norm_num)) (by norm_num))
    (abs_nonneg _)

theorem dyadicCofactorLogGrowthCoefficient_nonneg :
    0 ≤ dyadicCofactorLogGrowthCoefficient := by
  unfold dyadicCofactorLogGrowthCoefficient
  exact add_nonneg
    (add_nonneg (Real.log_pos one_lt_two).le (abs_nonneg _))
    (Real.log_pos (by norm_num : (1 : Real) < 3)).le

theorem dyadicCenterTwoTotalGrowthConstant_nonneg :
    0 ≤ dyadicCenterTwoTotalGrowthConstant := by
  unfold dyadicCenterTwoTotalGrowthConstant
  positivity [dyadicCofactorFixedGrowthCoefficient_nonneg,
    dyadicCofactorLogGrowthCoefficient_nonneg,
    spectralMultiplicityConstant_nonneg]

/-- Elementary exponential domination used for both logarithmic factors. -/
theorem natCast_add_two_le_two_pow (n : Nat) :
    ((n + 2 : Nat) : Real) ≤ (2 : Real) ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        (((n + 1 + 2 : Nat) : Real)) ≤
            2 * ((n + 2 : Nat) : Real) := by
              push_cast
              linarith
        _ ≤ 2 * (2 : Real) ^ (n + 2) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : Real) ^ (n + 1 + 2) := by
          rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
          ring

theorem natCast_add_four_le_two_pow (n : Nat) :
    ((n + 4 : Nat) : Real) ≤ (2 : Real) ^ (n + 4) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        (((n + 1 + 4 : Nat) : Real)) ≤
            2 * ((n + 4 : Nat) : Real) := by
              push_cast
              linarith
        _ ≤ 2 * (2 : Real) ^ (n + 4) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : Real) ^ (n + 1 + 4) := by
          rw [show n + 1 + 4 = (n + 4) + 1 by omega, pow_succ]
          ring

/-- The already-proved `R log R` estimate admits the geometric relaxation
used here as a numerical inequality on its exponent. -/
theorem xiDyadicRLogRGrowthExponent_le_three_pow (n : Nat) :
    xiDyadicRLogRGrowthExponent n ≤
      (xiGrowthFixedConstant + 1 + 192) * (3 : Real) ^ n := by
  have hmain : ((n + 4 : Nat) : Real) * (2 : Real) ^ (n + 4) ≤
      64 * (3 : Real) ^ n := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      nat_add_four_mul_two_pow_le_three_pow n
  have hpow : (1 : Real) ≤ (2 : Real) ^ (n + 4) :=
    one_le_pow₀ (by norm_num)
  have hk : 0 ≤ ((n + 4 : Nat) : Real) := Nat.cast_nonneg _
  have hlinear : ((n + 4 : Nat) : Real) ≤
      ((n + 4 : Nat) : Real) * (2 : Real) ^ (n + 4) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hk
  have hraw : xiDyadicRLogRGrowthExponent n ≤
      xiGrowthFixedConstant + 1 + 192 * (3 : Real) ^ n := by
    unfold xiDyadicRLogRGrowthExponent
    nlinarith
  have hthree : (1 : Real) ≤ (3 : Real) ^ n :=
    one_le_pow₀ (by norm_num)
  have hfixed : 0 ≤ xiGrowthFixedConstant + 1 :=
    add_nonneg xiGrowthFixedConstant_nonneg zero_le_one
  calc
    xiDyadicRLogRGrowthExponent n ≤
        xiGrowthFixedConstant + 1 + 192 * (3 : Real) ^ n := hraw
    _ ≤ (xiGrowthFixedConstant + 1 + 192) * (3 : Real) ^ n := by
      nlinarith [mul_le_mul_of_nonneg_left hthree hfixed]

/-- Logarithmic size of the center-`2` factor radius. -/
theorem log_dyadicCofactorFactorRadius_le (n : Nat) :
    Real.log (dyadicCofactorFactorRadius n) ≤
      Real.log 2 * (2 : Real) ^ (n + 4) := by
  have hlog := Real.log_le_log (dyadicCofactorFactorRadius_pos n)
    (dyadicCofactorFactorRadius_le n)
  calc
    Real.log (dyadicCofactorFactorRadius n) ≤
        Real.log ((2 : Real) ^ (n + 4)) := hlog
    _ = ((n + 4 : Nat) : Real) * Real.log 2 := by
      rw [Real.log_pow]
    _ ≤ (2 : Real) ^ (n + 4) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (natCast_add_four_le_two_pow n)
        (Real.log_pos one_lt_two).le
    _ = Real.log 2 * (2 : Real) ^ (n + 4) := by ring

/-- The reciprocal radial gap costs only a logarithmic factor.  The finite
grid denominator is first bounded multiplicatively, so taking `log` retains
linear-in-`n` growth instead of spuriously squaring the divisor mass. -/
theorem neg_log_dyadicCofactorRadialGap_le (n : Nat) :
    -Real.log (dyadicCofactorRadialGap n) ≤
      (|Real.log (4 * (spectralMultiplicityConstant + 2))| +
        Real.log 3) * (2 : Real) ^ (n + 2) := by
  let p : Real := (3 : Real) ^ (n + 2)
  let C : Real := 4 * (spectralMultiplicityConstant + 2)
  have hpPos : 0 < p := by dsimp only [p]; positivity
  have hpOne : 1 ≤ p := by
    dsimp only [p]
    exact one_le_pow₀ (by norm_num)
  have hCPos : 0 < C := by
    dsimp only [C]
    have hK := spectralMultiplicityConstant_nonneg
    positivity
  have hdenPos : 0 < 4 * (dyadicCofactorMassBound n + 2) := by
    have hmass := dyadicCofactorMassBound_nonneg n
    positivity
  have hmassExpand : dyadicCofactorMassBound n =
      spectralMultiplicityConstant * p := by
    rfl
  have hinside : dyadicCofactorMassBound n + 2 ≤
      (spectralMultiplicityConstant + 2) * p := by
    rw [hmassExpand]
    calc
      spectralMultiplicityConstant * p + 2 ≤
          spectralMultiplicityConstant * p + 2 * p := by
        exact add_le_add_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hpOne (by norm_num : (0 : Real) ≤ 2)) _
      _ = (spectralMultiplicityConstant + 2) * p := by ring
  have hden : 4 * (dyadicCofactorMassBound n + 2) ≤ C * p := by
    dsimp only [C]
    calc
      4 * (dyadicCofactorMassBound n + 2) ≤
          4 * ((spectralMultiplicityConstant + 2) * p) :=
        mul_le_mul_of_nonneg_left hinside (by norm_num : (0 : Real) ≤ 4)
      _ = 4 * (spectralMultiplicityConstant + 2) * p := by ring
  have hlogDen := Real.log_le_log hdenPos hden
  have hgapEq : -Real.log (dyadicCofactorRadialGap n) =
      Real.log (4 * (dyadicCofactorMassBound n + 2)) := by
    unfold dyadicCofactorRadialGap
    rw [one_div, Real.log_inv]
    ring
  have hlogProduct : Real.log (C * p) =
      Real.log C + ((n + 2 : Nat) : Real) * Real.log 3 := by
    rw [Real.log_mul hCPos.ne' hpPos.ne']
    dsimp only [p]
    rw [Real.log_pow]
  have hlinear : ((n + 2 : Nat) : Real) * Real.log 3 ≤
      (2 : Real) ^ (n + 2) * Real.log 3 :=
    mul_le_mul_of_nonneg_right (natCast_add_two_le_two_pow n)
      (Real.log_pos (by norm_num : (1 : Real) < 3)).le
  have hpowOne : (1 : Real) ≤ (2 : Real) ^ (n + 2) :=
    one_le_pow₀ (by norm_num)
  have hfixed : Real.log C ≤
      |Real.log C| * (2 : Real) ^ (n + 2) := by
    exact (le_abs_self _).trans
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpowOne (abs_nonneg (Real.log C)))
  rw [hgapEq]
  calc
    Real.log (4 * (dyadicCofactorMassBound n + 2)) ≤
        Real.log (C * p) := hlogDen
    _ = Real.log C + ((n + 2 : Nat) : Real) * Real.log 3 := hlogProduct
    _ ≤ |Real.log C| * (2 : Real) ^ (n + 2) +
          (2 : Real) ^ (n + 2) * Real.log 3 := add_le_add hfixed hlinear
    _ = (|Real.log (4 * (spectralMultiplicityConstant + 2))| +
          Real.log 3) * (2 : Real) ^ (n + 2) := by
      dsimp only [C]
      ring

/-- Both logarithmic penalties fit one `2^(n+4)` envelope. -/
theorem dyadicCofactor_log_penalty_le (n : Nat) :
    Real.log (dyadicCofactorFactorRadius n) -
        Real.log (dyadicCofactorRadialGap n) ≤
      dyadicCofactorLogGrowthCoefficient * (2 : Real) ^ (n + 4) := by
  have hR := log_dyadicCofactorFactorRadius_le n
  have hgap := neg_log_dyadicCofactorRadialGap_le n
  have hp : (2 : Real) ^ (n + 2) ≤ (2 : Real) ^ (n + 4) :=
    pow_right_mono₀ (by norm_num) (by omega)
  have hgapCoeff : 0 ≤
      |Real.log (4 * (spectralMultiplicityConstant + 2))| +
        Real.log 3 :=
    add_nonneg (abs_nonneg _)
      (Real.log_pos (by norm_num : (1 : Real) < 3)).le
  calc
    Real.log (dyadicCofactorFactorRadius n) -
        Real.log (dyadicCofactorRadialGap n) =
        Real.log (dyadicCofactorFactorRadius n) +
          (-Real.log (dyadicCofactorRadialGap n)) := by ring
    _ ≤ Real.log 2 * (2 : Real) ^ (n + 4) +
        (|Real.log (4 * (spectralMultiplicityConstant + 2))| +
          Real.log 3) * (2 : Real) ^ (n + 2) := add_le_add hR hgap
    _ ≤ Real.log 2 * (2 : Real) ^ (n + 4) +
        (|Real.log (4 * (spectralMultiplicityConstant + 2))| +
          Real.log 3) * (2 : Real) ^ (n + 4) := by
      gcongr
    _ = dyadicCofactorLogGrowthCoefficient *
        (2 : Real) ^ (n + 4) := by
      unfold dyadicCofactorLogGrowthCoefficient
      ring

/-- A transparent geometric majorant for the Borel real-part budget. -/
noncomputable def dyadicCofactorBorelGeometricMajorant (n : Nat) : Real :=
  dyadicCofactorFixedGrowthCoefficient * (3 : Real) ^ n +
    spectralMultiplicityConstant * (3 : Real) ^ (n + 2) *
      (dyadicCofactorLogGrowthCoefficient * (2 : Real) ^ (n + 4))

theorem dyadicCofactorBorelRealBound_le_geometricMajorant (n : Nat) :
    dyadicCofactorBorelRealBound n ≤
      dyadicCofactorBorelGeometricMajorant n := by
  have hthree : (1 : Real) ≤ (3 : Real) ^ n :=
    one_le_pow₀ (by norm_num)
  have habs : |Real.log ‖completedRiemannXi 2‖| ≤
      |Real.log ‖completedRiemannXi 2‖| * (3 : Real) ^ n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hthree (abs_nonneg _)
  have hfixed := xiDyadicRLogRGrowthExponent_le_three_pow n
  have hfirst : xiDyadicRLogRGrowthExponent n +
      |Real.log ‖completedRiemannXi 2‖| ≤
      dyadicCofactorFixedGrowthCoefficient * (3 : Real) ^ n := by
    calc
      xiDyadicRLogRGrowthExponent n +
          |Real.log ‖completedRiemannXi 2‖| ≤
          (xiGrowthFixedConstant + 1 + 192) * (3 : Real) ^ n +
            |Real.log ‖completedRiemannXi 2‖| * (3 : Real) ^ n :=
        add_le_add hfixed habs
      _ = dyadicCofactorFixedGrowthCoefficient * (3 : Real) ^ n := by
        unfold dyadicCofactorFixedGrowthCoefficient
        ring
  have hlog := dyadicCofactor_log_penalty_le n
  have hmass : 0 ≤ dyadicCofactorMassBound n :=
    dyadicCofactorMassBound_nonneg n
  unfold dyadicCofactorBorelRealBound dyadicCofactorBorelGeometricMajorant
  have hweighted := mul_le_mul_of_nonneg_left hlog hmass
  unfold dyadicCofactorMassBound at hweighted
  exact add_le_add hfirst hweighted

/-- The cofactor logarithmic derivative has a base-`12` geometric bound. -/
theorem dyadicCofactorLogDerivBound_le_twelve_pow (n : Nat) :
    dyadicCofactorLogDerivBound n ≤
      (64 * dyadicCofactorFixedGrowthCoefficient +
        9216 * spectralMultiplicityConstant *
          dyadicCofactorLogGrowthCoefficient) * (12 : Real) ^ n := by
  have hbaseThree : 0 ≤ (3 : Real) ^ n := by positivity
  have hbaseTwo : 0 ≤ (2 : Real) ^ n := by positivity
  have hmajorNonneg : 0 ≤ dyadicCofactorBorelGeometricMajorant n := by
    unfold dyadicCofactorBorelGeometricMajorant
    positivity [dyadicCofactorFixedGrowthCoefficient_nonneg,
      dyadicCofactorLogGrowthCoefficient_nonneg,
      spectralMultiplicityConstant_nonneg]
  have hB : dyadicCofactorBase n + 3 ≤ (2 : Real) ^ (n + 3) := by
    unfold dyadicCofactorBase
    have hp : (4 : Real) ≤ (2 : Real) ^ (n + 2) :=
      dyadicCofactorBase_ge_four n
    have heq : (2 : Real) ^ (n + 3) =
        2 * (2 : Real) ^ (n + 2) := by
      rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
      ring
    rw [heq]
    linarith
  have hraw : dyadicCofactorLogDerivBound n ≤
      8 * dyadicCofactorBorelGeometricMajorant n *
        (2 : Real) ^ (n + 3) := by
    have hbaseNonneg : 0 ≤ dyadicCofactorBase n + 3 := by
      linarith [dyadicCofactorBase_ge_four n]
    unfold dyadicCofactorLogDerivBound
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left
        (dyadicCofactorBorelRealBound_le_geometricMajorant n) (by norm_num))
      hB hbaseNonneg (mul_nonneg (by norm_num) hmajorNonneg)
  have hSix : (3 : Real) ^ n * (2 : Real) ^ n ≤ (12 : Real) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hTwelve : (3 : Real) ^ n * ((2 : Real) ^ n * (2 : Real) ^ n) =
      (12 : Real) ^ n := by
    rw [show (12 : Real) = 3 * (2 * 2) by norm_num, mul_pow, mul_pow]
  have hfixedNonneg := dyadicCofactorFixedGrowthCoefficient_nonneg
  have hlogNonneg := dyadicCofactorLogGrowthCoefficient_nonneg
  have hKnonneg := spectralMultiplicityConstant_nonneg
  calc
    dyadicCofactorLogDerivBound n ≤
        8 * dyadicCofactorBorelGeometricMajorant n *
          (2 : Real) ^ (n + 3) := hraw
    _ = 64 * dyadicCofactorFixedGrowthCoefficient *
          ((3 : Real) ^ n * (2 : Real) ^ n) +
        9216 * spectralMultiplicityConstant *
          dyadicCofactorLogGrowthCoefficient *
          ((3 : Real) ^ n * ((2 : Real) ^ n * (2 : Real) ^ n)) := by
      unfold dyadicCofactorBorelGeometricMajorant
      rw [show (3 : Real) ^ (n + 2) = 9 * (3 : Real) ^ n by
        rw [pow_add]; ring]
      rw [show (2 : Real) ^ (n + 4) = 16 * (2 : Real) ^ n by
        rw [pow_add]; ring]
      rw [show (2 : Real) ^ (n + 3) = 8 * (2 : Real) ^ n by
        rw [pow_add]; ring]
      ring
    _ ≤ 64 * dyadicCofactorFixedGrowthCoefficient * (12 : Real) ^ n +
        9216 * spectralMultiplicityConstant *
          dyadicCofactorLogGrowthCoefficient * (12 : Real) ^ n := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hSix
          (mul_nonneg (by norm_num) hfixedNonneg))
        (le_of_eq (congrArg
          (fun y : Real => 9216 * spectralMultiplicityConstant *
            dyadicCofactorLogGrowthCoefficient * y) hTwelve))
    _ = (64 * dyadicCofactorFixedGrowthCoefficient +
          9216 * spectralMultiplicityConstant *
            dyadicCofactorLogGrowthCoefficient) * (12 : Real) ^ n := by ring

/-- The finite principal part also fits the same base-`12` scale. -/
theorem dyadicCenterTwoPrincipalBound_le_twelve_pow (n : Nat) :
    dyadicCenterTwoPrincipalBound n ≤
      (108 * spectralMultiplicityConstant ^ 2 +
        72 * spectralMultiplicityConstant) * (12 : Real) ^ n := by
  have hK := spectralMultiplicityConstant_nonneg
  have hNine : (9 : Real) ^ n ≤ (12 : Real) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hThree : (3 : Real) ^ n ≤ (12 : Real) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  calc
    dyadicCenterTwoPrincipalBound n =
        108 * spectralMultiplicityConstant ^ 2 * (9 : Real) ^ n +
          72 * spectralMultiplicityConstant * (3 : Real) ^ n := by
      unfold dyadicCenterTwoPrincipalBound dyadicCofactorMassBound
      rw [show (3 : Real) ^ (n + 2) = 9 * (3 : Real) ^ n by
        rw [pow_add]; ring]
      rw [show (3 : Real) ^ (n + 1) = 3 * (3 : Real) ^ n by
        rw [pow_add]; ring]
      rw [show (9 : Real) ^ n = (3 : Real) ^ n * (3 : Real) ^ n by
        rw [← mul_pow]
        norm_num]
      ring
    _ ≤ 108 * spectralMultiplicityConstant ^ 2 * (12 : Real) ^ n +
        72 * spectralMultiplicityConstant * (12 : Real) ^ n := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hNine
          (mul_nonneg (by norm_num) (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left hThree
          (mul_nonneg (by norm_num) hK))
    _ = (108 * spectralMultiplicityConstant ^ 2 +
          72 * spectralMultiplicityConstant) * (12 : Real) ^ n := by ring

/-- Final pointwise geometric envelope for the full same-owner horizontal
logarithmic derivative. -/
theorem dyadicCenterTwoXiLogDerivBound_le_twelve_pow (n : Nat) :
    dyadicCenterTwoXiLogDerivBound n ≤
      dyadicCenterTwoTotalGrowthConstant * (12 : Real) ^ n := by
  unfold dyadicCenterTwoXiLogDerivBound
  calc
    dyadicCenterTwoPrincipalBound n + dyadicCofactorLogDerivBound n ≤
        (108 * spectralMultiplicityConstant ^ 2 +
          72 * spectralMultiplicityConstant) * (12 : Real) ^ n +
        (64 * dyadicCofactorFixedGrowthCoefficient +
          9216 * spectralMultiplicityConstant *
            dyadicCofactorLogGrowthCoefficient) * (12 : Real) ^ n :=
      add_le_add (dyadicCenterTwoPrincipalBound_le_twelve_pow n)
        (dyadicCofactorLogDerivBound_le_twelve_pow n)
    _ = dyadicCenterTwoTotalGrowthConstant * (12 : Real) ^ n := by
      unfold dyadicCenterTwoTotalGrowthConstant
      ring

/-- The base-`12` majorant divided by the fourth power of the dyadic base
height is a constant multiple of `(3/4)^n`. -/
theorem tendsto_twelve_pow_div_dyadicBase_pow_four :
    Tendsto
      (fun n : Nat =>
        dyadicCenterTwoTotalGrowthConstant * (12 : Real) ^ n /
          dyadicCofactorBase n ^ 4)
      atTop (nhds 0) := by
  have hgeom : Tendsto (fun n : Nat => ((3 / 4 : Real) ^ n))
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled := hgeom.const_mul (dyadicCenterTwoTotalGrowthConstant / 256)
  convert hscaled using 1
  · funext n
    have hfourPow : (4 : Real) ^ n = ((2 : Real) ^ n) ^ 2 := by
      calc
        (4 : Real) ^ n = ((2 : Real) ^ 2) ^ n := by norm_num
        _ = (2 : Real) ^ (2 * n) := (pow_mul (2 : Real) 2 n).symm
        _ = (2 : Real) ^ (n * 2) := by rw [Nat.mul_comm]
        _ = ((2 : Real) ^ n) ^ 2 := pow_mul (2 : Real) n 2
    unfold dyadicCofactorBase
    rw [show (2 : Real) ^ (n + 2) = 4 * (2 : Real) ^ n by
      rw [pow_add]; ring]
    rw [show (12 : Real) ^ n = (3 : Real) ^ n * (4 : Real) ^ n by
      rw [← mul_pow]
      norm_num]
    rw [div_pow]
    field_simp
    norm_num
    rw [hfourPow]
    ring
  · simp

/-- Canonical choice of one same-owner horizontal datum at every scale. -/
noncomputable def selectedDyadicCenterTwoHorizontalData (n : Nat) :
    DyadicCenterTwoHorizontalData n :=
  Classical.choice (exists_dyadicCenterTwoHorizontalData n)

noncomputable def selectedDyadicCenterTwoHeight (n : Nat) : Real :=
  (selectedDyadicCenterTwoHorizontalData n).height

/-- The actual selected same-owner xi envelope is `o(T_n^4)`. -/
theorem tendsto_dyadicCenterTwoXiLogDerivBound_div_height_pow_four :
    Tendsto
      (fun n : Nat => dyadicCenterTwoXiLogDerivBound n /
        selectedDyadicCenterTwoHeight n ^ 4)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (dyadicCenterTwoXiLogDerivBound_nonneg n)
      (pow_nonneg (selectedDyadicCenterTwoHorizontalData n).height_pos.le 4)
  · intro n
    let H := selectedDyadicCenterTwoHorizontalData n
    have hbasePos : 0 < dyadicCofactorBase n := by
      unfold dyadicCofactorBase
      positivity
    have hheight : dyadicCofactorBase n ≤ H.height := H.height_lower.le
    have hpowers : dyadicCofactorBase n ^ 4 ≤ H.height ^ 4 :=
      pow_le_pow_left₀ hbasePos.le hheight 4
    have hnum : dyadicCenterTwoXiLogDerivBound n ≤
        dyadicCenterTwoTotalGrowthConstant * (12 : Real) ^ n :=
      dyadicCenterTwoXiLogDerivBound_le_twelve_pow n
    have hfirst : dyadicCenterTwoXiLogDerivBound n / H.height ^ 4 ≤
        (dyadicCenterTwoTotalGrowthConstant * (12 : Real) ^ n) /
          H.height ^ 4 :=
      div_le_div_of_nonneg_right hnum (pow_nonneg H.height_pos.le 4)
    have hsecond :
        (dyadicCenterTwoTotalGrowthConstant * (12 : Real) ^ n) /
            H.height ^ 4 ≤
          (dyadicCenterTwoTotalGrowthConstant * (12 : Real) ^ n) /
            dyadicCofactorBase n ^ 4 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg dyadicCenterTwoTotalGrowthConstant_nonneg (by positivity))
        (pow_pos hbasePos 4) hpowers
    simpa only [selectedDyadicCenterTwoHeight, H] using hfirst.trans hsecond
  · exact tendsto_twelve_pow_div_dyadicBase_pow_four

end
end C1XiCenterTwoHorizontalDecay
end Source
end ConnesWeilRH
