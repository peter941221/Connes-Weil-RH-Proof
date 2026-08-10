import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import ConnesWeilRH.Dev.GammaArgBricks
import ConnesWeilRH.Dev.GammaArgSum
/-!
# Weierstrass factor arguments for the Gamma argument at 1+I/2 (docs/941)
Certifies axiom-clean the principal-argument additivity of the finite
Weierstrass-type factors used by the Gamma-argument identity at the finite-S
base point `a = 1` (base point `1 + I/2`):
    arg( e^{I*theta} / (1 + I*x) ) = theta - atan(x)          (as Real.Angle)
and lifts it to arbitrary finite products via
`GammaArgSum.arg_prod_coe_angle`.  This is the factor-level spine of
`SSeriesSandwich` / `PhaseGateSandwich`; the infinite-product limit that
identifies it with the Gamma argument is the open analytic leaf (docs/940).
All lemmas are axiom-clean off mathlib foundations (`[propext,
Classical.choice, Quot.sound]`, 0 sorry). RH NOT claimed.
-/
open Complex
namespace ConnesWeilRH
namespace Dev
namespace WeierstrassFactorArg
/-- Argument of a pure unit phase `e^{I*theta}`, as `Real.Angle` (the Branch
reduces to theta through the 2*pi quotient). -/
lemma arg_exp_mul_I_angle (θ : Real) :
    ((Complex.exp (θ * Complex.I)).arg : Real.Angle) = θ := by
  rw [Complex.arg_exp_mul_I]
  exact Real.Angle.coe_toIocMod θ (-Real.pi)
/-- Single Weierstrass factor: `arg( e^{I*theta} / (1 + I*x) ) = theta - atan x`
(as `Real.Angle`) for `0 <= x`. -/
theorem arg_factor_coe_angle {x : Real} (hx : 0 <= x) (θ : Real) :
    ((Complex.exp (θ * Complex.I) / ((1 : Complex) + Complex.I * (x : Complex))).arg : Real.Angle)
      = θ - Real.arctan x := by
  have hden : (1 : Complex) + Complex.I * (x : Complex) ≠ 0 := by
    intro h
    have hre : ((1 : Complex) + Complex.I * (x : Complex)).re = 0 := congrArg Complex.re h
    norm_num at hre
  have hnum : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.arg_div_coe_angle hnum hden]
  rw [arg_exp_mul_I_angle θ]
  rw [GammaArgBricks.arg_one_add_I_mul hx]
/-- The concrete factor the Gamma product needs first: `n = 2`,
   `theta = 1/2`, factor base `1 + I/2`. -/
theorem arg_factor_half :
    ((Complex.exp (((1 / 2 : Real) : Complex) * Complex.I) /
        ((1 : Complex) + Complex.I * ((1 / 2 : Real) : Complex))).arg : Real.Angle)
      = (1 / 2 : Real) - Real.arctan (1 / 2 : Real) := by
  exact arg_factor_coe_angle (by norm_num : (0 : Real) <= 1 / 2) (1 / 2 : Real)
/-- Argument of a point `x + I*y` (0 < x) equals `atan(y/x)`: the positive
real part puts arg in the principal branch `(-pi/2, pi/2)`. -/
lemma arg_add_mul_I {x y : Real} (hx : 0 < x) :
    ((x : Complex) + Complex.I * (y : Complex)).arg = Real.arctan (y / x) := by
  set z : Complex := (x : Complex) + Complex.I * (y : Complex)
  have hrepos : 0 < z.re := by
    simpa [z] using hx
  have habs : |z.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrepos)
  have hzgt : -(Real.pi / 2) < z.arg := (abs_lt.mp habs).1
  have hzlt : z.arg < Real.pi / 2 := (abs_lt.mp habs).2
  have htan : Real.tan (z.arg) = y / x := by
    rw [Complex.tan_arg z]
    simp [z]
  have ha1 : -(Real.pi / 2) < Real.arctan (y / x) := (Real.arctan_mem_Ioo (y / x)).1
  have ha2 : Real.arctan (y / x) < Real.pi / 2 := (Real.arctan_mem_Ioo (y / x)).2
  change z.arg = Real.arctan (y / x)
  apply Real.tan_inj_of_lt_of_lt_pi_div_two hzgt hzlt ha1 ha2
  rw [Real.tan_arctan]
  exact htan
/-- Argument of an exponential `e^{r + I*s}` is `s` (as `Real.Angle`). -/
lemma arg_exp_add_mul_I_angle (r s : Real) :
    ((Complex.exp ((r : Complex) + Complex.I * (s : Complex))).arg : Real.Angle) = s := by
  rw [Complex.arg_exp]
  simp


/-- Arg of the exponential half of the Weylstrass Gamma factor at `z = 1 + I/2`:
   `e^{-z/n}` with `z/n = 1/n + I/(2n)` has argument `-1/(2n)` (as `Real.Angle`).
   This is the `-1/(2n)` component that, summed over the finite product, becomes
   the `S2 = 1/(2(n+1)) - atan(1/(2(n+1)))` series (see `SSandwich`). -/
lemma arg_exp_neg_z_div_n (u : Real) :
    ((Complex.exp (((-1 / u : Real) : Complex)
        + Complex.I * (((-1 / (2 * u) : Real)) : Complex))).arg : Real.Angle)
      = ((-1 / (2 * u) : Real) : Real.Angle) := by
  rw [arg_exp_add_mul_I_angle (-1 / u) (-1 / (2 * u))]


/-- Arg of the imaginary-direction factor `(u+1)/u + I/(2u)` (the `1 + z/n`
   part of the Weylstrass Gamma factor with `u = n`) equals
   `atan(1/(2u+2))`, the `S`-series summand under `SSandwich`. -/
lemma arg_gamma_imag (u : Real) (hu : 0 < u) :
    ((((u + 1) / u : Real) : Complex)
        + Complex.I * (((1 / (2 * u) : Real)) : Complex)).arg
      = Real.arctan ((1 / (2 * (u + 1))) : Real) := by
  rw [arg_add_mul_I (x := (u + 1) / u) (y := 1 / (2 * u)) (by positivity)]
  congr 1
  field_simp
/-- The full Weylstrass Gamma factor at `z = 1 + I/2` for scale `u > 0`:
   `w(u) = exp( -z/u ) * (1 + z/u)`, with `z/u = 1/u + I/(2u)`. -/
noncomputable def weylFactor (u : Real) : Complex :=
  Complex.exp (((-1 / u : Real) : Complex)
        + Complex.I * (((-1 / (2 * u)) : Real) : Complex)) *
    ((((u + 1) / u : Real) : Complex)
        + Complex.I * (((1 / (2 * u)) : Real) : Complex))

/-- Argument of the full Weylstrass factor at the base point `z = 1 + I/2`:
   `arg w(u) = -1/(2u) + atan(1/(2u+2))` (as `Real.Angle`). -/
theorem arg_weylFactor (u : Real) (hu : 0 < u) :
    ((weylFactor u).arg : Real.Angle)
      = (-1 / (2 * u) + Real.arctan (1 / (2 * (u + 1))) : Real) := by
  unfold weylFactor
  have hnzIm : ((((u + 1) / u : Real) : Complex)
          + Complex.I * (((1 / (2 * u)) : Real) : Complex)) ≠ 0 := by
    intro hzero
    have hz : ((((u + 1) / u : Real) : Complex)
          + Complex.I * (((1 / (2 * u)) : Real) : Complex)).re = 0 :=
      congrArg Complex.re hzero
    have hreval : ((((u + 1) / u : Real) : Complex)
          + Complex.I * (((1 / (2 * u)) : Real) : Complex)).re = (u + 1) / u := by
      simp [Complex.add_re, Complex.mul_re]
    have hzero2 : (u + 1) / u = 0 := by
      rw [hreval] at hz
      exact hz
    have hpos : 0 < (u + 1) / u := by positivity
    linarith
  rw [Complex.arg_mul_coe_angle (Complex.exp_ne_zero _) hnzIm]
  rw [arg_exp_neg_z_div_n u]
  rw [arg_gamma_imag u hu]
  rfl
/-- The `1 + z/n` half of the Weierstrass factor is non-zero for `0 < u`. -/
lemma weylFactorIm_nonzero (u : Real) (hu : 0 < u) :
    ((((u + 1) / u : Real) : Complex) +
        Complex.I * (((1 / (2 * u)) : Real) : Complex)) ≠ 0 := by
  intro hzero
  have hz : (((((u + 1) / u : Real) : Complex) +
        Complex.I * (((1 / (2 * u)) : Real) : Complex)).re) = 0 :=
    congrArg Complex.re hzero
  have hreval : (((((u + 1) / u : Real) : Complex) +
        Complex.I * (((1 / (2 * u)) : Real) : Complex)).re) = (u + 1) / u := by
    simp [Complex.add_re, Complex.mul_re]
  have hzero2 : (u + 1) / u = 0 := by
    rw [hreval] at hz
    exact hz
  have hpos : 0 < (u + 1) / u := by positivity
  linarith

/-- A single Weierstrass factor is non-zero for `0 < u`. -/
lemma weylFactor_ne_zero (u : Real) (hu : 0 < u) : weylFactor u ≠ 0 := by
  unfold weylFactor
  exact mul_ne_zero (Complex.exp_ne_zero _) (weylFactorIm_nonzero u hu)

/-- The per-factor argument value `-1/(2u) + atan(1/(2(u+1)))`. -/
noncomputable def weylArgNum (u : Real) : Real :=
  -1 / (2 * u) + Real.arctan (1 / (2 * (u + 1)))

/-- The principal argument (as `Real.Angle`) of a finite product of Weierstrass
factors equals the sum of their per-factor arguments.  This is the finite
partial-product preimage of `SSeriesSandwich.S_eq_S2_add_atan_half` at the
base point `1 + I/2`, indexed over real scales. -/
theorem arg_weylFactor_prod_coe_angle (t : Finset ℝ)
    (ht : ∀ i : ℝ, i ∈ t → 0 < i) :
    ((Finset.prod t (fun i : Real => weylFactor i)).arg : Real.Angle)
      = Finset.sum t (fun i : Real => (weylArgNum i : Real.Angle)) := by
  have hnone : ∀ i ∈ t, weylFactor i ≠ 0 := fun i hi => weylFactor_ne_zero i (ht i hi)
  have hsum : ((Finset.prod t (fun i : Real => weylFactor i)).arg : Real.Angle)
      = Finset.sum t (fun i : Real => (weylFactor i).arg) :=
    GammaArgSum.arg_prod_coe_angle t (fun i : Real => weylFactor i) hnone
  rw [hsum]
  rw [GammaArgSum.real_sum_coe_angle t (fun i : Real => (weylFactor i).arg)]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [weylArgNum] using arg_weylFactor i (ht i hi)
end WeierstrassFactorArg
end Dev
end ConnesWeilRH