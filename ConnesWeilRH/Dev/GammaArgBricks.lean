import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Gamma-argument bricks (docs/940, docs/941)

Verified, axiom-clean building blocks for the Weierstrass log-Gamma argument
identity at the finite-S base point `1 + I/2`:

    arg(Gamma(1+I/2)) = -gamma/2 - atan(1/2) + Sum_n [ 1/(2n) - atan(1/(2(n+1))) ].

Each factor `1 + I/n` of the Weierstrass product has principal argument
`Real.arctan (1/n)`.  This module certifies that general fact
`arg_one_add_I_mul` (for `0 <= x`) axiom-clean, and instantiates it at the two
points the Gamma product needs (`x = 1/2`, `x = 1/(2n)`).  The
`SSeriesSandwich`/`PhaseGateSandwich`/`ArctanCert` modules already bound the
right-hand series; the connection is the open analytic leaf (docs/940).

All lemmas here are axiom-clean off mathlib foundations. RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Dev
namespace GammaArgBricks

/-- `arg (1 + I*x) = arctan x` for `0 <= x` (principal branch, re>0). -/
lemma arg_one_add_I_mul {x : Real} (hx : 0 <= x) :
    ((1 : Complex) + Complex.I * (x : Complex)).arg = Real.arctan x := by
  set z : Complex := (1 : Complex) + Complex.I * (x : Complex)
  have hrepos : 0 < z.re := by simp [z]
  have habs : |z.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrepos)
  have hzgt : -(Real.pi / 2) < z.arg := (abs_lt.mp habs).1
  have hzlt : z.arg < Real.pi / 2 := (abs_lt.mp habs).2
  have htan : Real.tan (z.arg) = x := by
    rw [Complex.tan_arg z]
    simp [z]
  have ha1 : -(Real.pi / 2) < Real.arctan x := (Real.arctan_mem_Ioo x).1
  have ha2 : Real.arctan x < Real.pi / 2 := (Real.arctan_mem_Ioo x).2
  change z.arg = Real.arctan x
  apply Real.tan_inj_of_lt_of_lt_pi_div_two hzgt hzlt ha1 ha2
  rw [Real.tan_arctan]
  exact htan

/-- `arg(1 + I/2) = arctan(1/2)`. -/
theorem arg_one_add_I_half :
    ((1 : Complex) + Complex.I * (((1 / 2 : Real) : Complex))).arg =
      Real.arctan (1 / 2 : Real) := by
  exact arg_one_add_I_mul (by norm_num : (0 : Real) <= 1 / 2)

/-- `arg(1 + I/(2n)) = arctan(1/(2n))` for `0 < n`. -/
theorem arg_one_add_I_div_two_nat (n : Nat) (hn : 0 < n) :
    ((1 : Complex) + Complex.I * (((1 : Real) / (2 * (n : Real)) : Real) : Complex)).arg =
      Real.arctan ((1 : Real) / (2 * (n : Real))) := by
  refine arg_one_add_I_mul ?_
  positivity
end GammaArgBricks
end Dev
end ConnesWeilRH

