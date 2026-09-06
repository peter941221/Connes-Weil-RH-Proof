import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# CC20 equation-(983) eigenvalue tail

This leaf formalizes only the exact arithmetic tail of the CC20 bound.  The
Rokhlin/CC20 estimate `|lambda(n)| <= bound983 n` remains an explicit
hypothesis at the consumer theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20EndpointEigenvalueTail983

/-- The paper's equation-(983) upper bound for the absolute prolate
eigenvalue. -/
noncomputable def bound983 (n : Nat) : Real :=
  (2 : Real) ^ (2 * n) *
    Real.pi ^ (((2 * n : Nat) : Real) + 1 / 2) *
      ((2 * n).factorial : Real) ^ 2 /
    (((4 * n).factorial : Real) *
      Real.Gamma (((2 * n : Nat) : Real) + 3 / 2))

/-- A factorial and double-factorial normal form of `bound983`, used only to
make the exact successor calculation tractable. -/
private noncomputable def coefficient983 (n : Nat) : Real :=
  (2 : Real) ^ (4 * n + 1) * Real.pi ^ (2 * n) *
      ((2 * n).factorial : Real) ^ 2 /
    (((4 * n).factorial : Real) *
      ((4 * n + 1).doubleFactorial : Real))

/-- The exact successor factor after the half-integer Gamma value is reduced
to factorials. -/
private noncomputable def ratio983 (n : Nat) : Real :=
  16 * Real.pi ^ 2 *
      (2 * (n : Real) + 2) ^ 2 * (2 * (n : Real) + 1) ^ 2 /
    ((4 * (n : Real) + 1) * (4 * (n : Real) + 2) *
      (4 * (n : Real) + 3) ^ 2 * (4 * (n : Real) + 4) *
      (4 * (n : Real) + 5))

private theorem pi_lt_twenty_two_div_seven :
    Real.pi < (22 : Real) / 7 := by
  calc
    Real.pi < 3.1416 := Real.pi_lt_d4
    _ < (22 : Real) / 7 := by norm_num

private theorem coefficient983_pos (n : Nat) : 0 < coefficient983 n := by
  unfold coefficient983
  positivity

private theorem bound983_eq_coefficient983 (n : Nat) :
    bound983 n = coefficient983 n := by
  have hodd : 2 * (2 * n) + 1 = 4 * n + 1 := by omega
  have hgamma := Real.Gamma_nat_add_one_add_half (2 * n)
  rw [hodd] at hgamma
  have hgamma' :
      Real.Gamma (((2 * n : Nat) : Real) + 3 / 2) =
        ((4 * n + 1).doubleFactorial : Real) * Real.sqrt Real.pi /
          (2 : Real) ^ (2 * n + 1) := by
    have hthreeHalves : (3 : Real) / 2 = 1 + 1 / 2 := by norm_num
    simpa only [hthreeHalves, add_assoc] using hgamma
  have hpi :
      Real.pi ^ (((2 * n : Nat) : Real) + 1 / 2) =
        Real.pi ^ (2 * n) * Real.sqrt Real.pi := by
    calc
      Real.pi ^ (((2 * n : Nat) : Real) + 1 / 2) =
          Real.pi ^ ((2 * n : Nat) : Real) * Real.pi ^ (1 / 2) :=
        Real.rpow_add Real.pi_pos _ _
      _ = Real.pi ^ (2 * n) * Real.sqrt Real.pi := by
        rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have htwo :
      (2 : Real) ^ (2 * n + 1) * (2 : Real) ^ (2 * n) =
        (2 : Real) ^ (4 * n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  unfold bound983 coefficient983
  rw [hpi, hgamma']
  field_simp
  nlinarith [htwo]

theorem bound983_two_eq :
    bound983 2 = 768 * Real.pi ^ 4 / 99225 := by
  rw [bound983_eq_coefficient983]
  norm_num [coefficient983, Nat.factorial, Nat.doubleFactorial]
  ring

theorem bound983_two_lt_one : bound983 2 < 1 := by
  rw [bound983_two_eq]
  have hpi4 : Real.pi ^ 4 < ((22 : Real) / 7) ^ 4 :=
    pow_lt_pow_left₀ pi_lt_twenty_two_div_seven Real.pi_pos.le (by norm_num)
  calc
    768 * Real.pi ^ 4 / 99225 <
        768 * ((22 : Real) / 7) ^ 4 / 99225 := by
          exact div_lt_div_of_pos_right
            (mul_lt_mul_of_pos_left hpi4 (by norm_num)) (by norm_num)
    _ < 1 := by norm_num

private theorem pi_sq_lt_ten : Real.pi ^ 2 < 10 := by
  have hpi2 : Real.pi ^ 2 < ((22 : Real) / 7) ^ 2 :=
    pow_lt_pow_left₀ pi_lt_twenty_two_div_seven Real.pi_pos.le (by norm_num)
  calc
    Real.pi ^ 2 < ((22 : Real) / 7) ^ 2 := hpi2
    _ < 10 := by norm_num

private theorem ratio983_polynomial_bound (x : Real) (hx : 2 <= x) :
    160 * (2 * x + 2) ^ 2 * (2 * x + 1) ^ 2 <
      (4 * x + 1) * (4 * x + 2) * (4 * x + 3) ^ 2 *
        (4 * x + 4) * (4 * x + 5) := by
  let z : Real := 4 * x ^ 2 + 6 * x + 2
  have hz : 30 <= z := by
    have hnonneg : 0 <= (x - 2) * (4 * x + 14) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp only [z]
    nlinarith
  have hzpos : 0 < z := by linarith
  have hrest : 0 < 16 * z ^ 2 - 48 * z - 3 := by
    have hnonneg : 0 <= (z - 30) * (z + 27) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hproduct : 0 < 4 * z * (16 * z ^ 2 - 48 * z - 3) := by
    positivity
  have hfactor :
      (4 * x + 1) * (4 * x + 2) * (4 * x + 3) ^ 2 *
          (4 * x + 4) * (4 * x + 5) -
        160 * (2 * x + 2) ^ 2 * (2 * x + 1) ^ 2 =
          4 * z * (16 * z ^ 2 - 48 * z - 3) := by
    dsimp only [z]
    ring
  nlinarith

private theorem ratio983_lt_one (n : Nat) (hn : 2 <= n) : ratio983 n < 1 := by
  unfold ratio983
  have hx : 2 <= (n : Real) := by exact_mod_cast hn
  have htail := ratio983_polynomial_bound (n : Real) hx
  have hfactorPos :
      0 < (2 * (n : Real) + 2) ^ 2 * (2 * (n : Real) + 1) ^ 2 := by
    positivity
  have hpi :
      16 * Real.pi ^ 2 *
          ((2 * (n : Real) + 2) ^ 2 * (2 * (n : Real) + 1) ^ 2) <
        160 * ((2 * (n : Real) + 2) ^ 2 * (2 * (n : Real) + 1) ^ 2) := by
    have hscaled : 16 * Real.pi ^ 2 < 16 * 10 :=
      mul_lt_mul_of_pos_left pi_sq_lt_ten (by norm_num)
    calc
      16 * Real.pi ^ 2 *
          ((2 * (n : Real) + 2) ^ 2 * (2 * (n : Real) + 1) ^ 2) <
          (16 * 10) *
            ((2 * (n : Real) + 2) ^ 2 * (2 * (n : Real) + 1) ^ 2) :=
        mul_lt_mul_of_pos_right hscaled hfactorPos
      _ = 160 * ((2 * (n : Real) + 2) ^ 2 *
          (2 * (n : Real) + 1) ^ 2) := by ring
  have hdenPos :
      0 < (4 * (n : Real) + 1) * (4 * (n : Real) + 2) *
        (4 * (n : Real) + 3) ^ 2 * (4 * (n : Real) + 4) *
          (4 * (n : Real) + 5) := by
    positivity
  have htail' :
      160 * ((2 * (n : Real) + 2) ^ 2 * (2 * (n : Real) + 1) ^ 2) <
        (4 * (n : Real) + 1) * (4 * (n : Real) + 2) *
          (4 * (n : Real) + 3) ^ 2 * (4 * (n : Real) + 4) *
            (4 * (n : Real) + 5) := by
    simpa only [mul_assoc] using htail
  apply (div_lt_iff₀ hdenPos).mpr
  simpa only [one_mul, mul_assoc] using hpi.trans htail'

private theorem coefficient983_succ_eq_ratio (n : Nat) :
    coefficient983 (n + 1) = ratio983 n * coefficient983 n := by
  have hpowTwo :
      (2 : Real) ^ (4 * (n + 1) + 1) =
        (2 : Real) ^ 4 * (2 : Real) ^ (4 * n + 1) := by
    rw [show 4 * (n + 1) + 1 = 4 + (4 * n + 1) by omega, pow_add]
  have hpowPi :
      Real.pi ^ (2 * (n + 1)) =
        Real.pi ^ 2 * Real.pi ^ (2 * n) := by
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, pow_add]
  have hfactorialTwo :
      (2 * (n + 1)).factorial =
        (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
    rw [show 2 * (n + 1) = 2 * n + 2 by omega]
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ]
    rw [show 2 * n + 1 = (2 * n) + 1 by omega, Nat.factorial_succ]
    ring
  have hfactorialFour :
      (4 * (n + 1)).factorial =
        (4 * n + 4) * (4 * n + 3) * (4 * n + 2) * (4 * n + 1) *
          (4 * n).factorial := by
    rw [show 4 * (n + 1) = 4 * n + 4 by omega]
    rw [show 4 * n + 4 = (4 * n + 3) + 1 by omega, Nat.factorial_succ]
    rw [show 4 * n + 3 = (4 * n + 2) + 1 by omega, Nat.factorial_succ]
    rw [show 4 * n + 2 = (4 * n + 1) + 1 by omega, Nat.factorial_succ]
    rw [show 4 * n + 1 = (4 * n) + 1 by omega, Nat.factorial_succ]
    ring
  have hdoubleFactorial :
      (4 * (n + 1) + 1).doubleFactorial =
        (4 * n + 5) * (4 * n + 3) * (4 * n + 1).doubleFactorial := by
    rw [show 4 * (n + 1) + 1 = 4 * n + 5 by omega]
    rw [show 4 * n + 5 = (4 * n + 3) + 2 by omega,
      Nat.doubleFactorial_add_two]
    rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega,
      Nat.doubleFactorial_add_two]
    ring
  unfold coefficient983 ratio983
  rw [hpowTwo, hpowPi, hfactorialTwo, hfactorialFour, hdoubleFactorial]
  push_cast
  field_simp
  ring

theorem bound983_succ_lt (n : Nat) (hn : 2 <= n) :
    bound983 (n + 1) < bound983 n := by
  calc
    bound983 (n + 1) = coefficient983 (n + 1) :=
      bound983_eq_coefficient983 (n + 1)
    _ = ratio983 n * coefficient983 n := coefficient983_succ_eq_ratio n
    _ < 1 * coefficient983 n :=
      mul_lt_mul_of_pos_right (ratio983_lt_one n hn) (coefficient983_pos n)
    _ = coefficient983 n := by ring
    _ = bound983 n := (bound983_eq_coefficient983 n).symm

theorem bound983_lt_one (n : Nat) (hn : 2 <= n) : bound983 n < 1 := by
  induction n, hn using Nat.le_induction with
  | base => exact bound983_two_lt_one
  | succ n hn ih => exact (bound983_succ_lt n hn).trans ih

theorem eigenvalue_sq_lt_one_of_bound983
    (eigenvalue : Nat -> Real)
    (htransfer : forall n, 2 <= n -> |eigenvalue n| <= bound983 n)
    (n : Nat) (hn : 2 <= n) :
    eigenvalue n ^ 2 < 1 := by
  apply (sq_lt_one_iff_abs_lt_one _).mpr
  exact (htransfer n hn).trans_lt (bound983_lt_one n hn)

end C1CC20EndpointEigenvalueTail983
end Source
end ConnesWeilRH
