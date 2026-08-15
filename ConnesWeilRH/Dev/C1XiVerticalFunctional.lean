import ConnesWeilRH.Dev.C1SpectralSummability
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# C1XiVerticalFunctional - the common contour owner for Gate 2

The arithmetic and zero-spectral sides of Gate 2 must meet through one
independently defined analytic object.  This module fixes that object at the
level needed by the later contour argument:

* `centeredLaplaceWeight F s` is the exact transform appearing at a xi zero;
* `symmetrizedLaplaceWeight F s` is invariant under `s \mapsto 1 - s`;
* `xiContourKernel F s` is the single-weight kernel whose residues read the
  multiplicity-weighted spectral terms;
* `xiRightLineKernel F s` is the reflected, symmetric kernel used after the
  two vertical sides are folded onto one right line;
* `truncatedXiVerticalFunctional F c T` is the oriented vertical-line
  integral, normalized by `2 * pi * I`.

No explicit-formula equality, limiting assertion, positivity statement, or RH
claim is assumed here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiVerticalFunctional

open MeasureTheory
open CC20ZetaCounting
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open scoped Interval

/-- The Laplace weight centered at the critical line.  At a source zero
`rho`, this is definitionally the transform used by `spectralTerm F rho`. -/
noncomputable def centeredLaplaceWeight
    (F : CompactLogTest) (s : Complex) : Complex :=
  CompactLogTest.laplaceAt F (s - (1 / 2 : Complex))

/-- The functional-equation-symmetric test weight. -/
noncomputable def symmetrizedLaplaceWeight
    (F : CompactLogTest) (s : Complex) : Complex :=
  centeredLaplaceWeight F s + centeredLaplaceWeight F (1 - s)

/-- The negative logarithmic derivative of the completed xi function. -/
noncomputable def negativeXiLogDeriv (s : Complex) : Complex :=
  -logDeriv completedRiemannXi s

/-- The single-weight contour kernel.  Its residue at a zero `rho` carries one
copy of `centeredLaplaceWeight F rho`, matching `spectralTerm F rho`. -/
noncomputable def xiContourKernel
    (F : CompactLogTest) (s : Complex) : Complex :=
  negativeXiLogDeriv s * centeredLaplaceWeight F s

/-- The right-line kernel obtained after folding the left edge of a rectangle
through `s ↦ 1 - s`.  The reflected weight is present here, not in the
zero-residue kernel, so the spectral sum is not counted twice. -/
noncomputable def xiRightLineKernel
    (F : CompactLogTest) (s : Complex) : Complex :=
  negativeXiLogDeriv s * symmetrizedLaplaceWeight F s

/-- Standard upward parametrization of a vertical line. -/
def verticalPoint (c t : Real) : Complex :=
  (c : Complex) + (t : Complex) * Complex.I

/-- The oriented integrand after the substitution `s = c + t * I`. -/
noncomputable def verticalIntegrand
    (F : CompactLogTest) (c t : Real) : Complex :=
  xiRightLineKernel F (verticalPoint c t) * Complex.I

/-- The normalized, symmetrically truncated upward vertical integral. -/
noncomputable def truncatedXiVerticalFunctional
    (F : CompactLogTest) (c T : Real) : Complex :=
  ((2 * Real.pi : Complex) * Complex.I)⁻¹ *
    ∫ t in (-T)..T, verticalIntegrand F c t

@[simp] theorem centeredLaplaceWeight_apply
    (F : CompactLogTest) (s : Complex) :
    centeredLaplaceWeight F s =
      CompactLogTest.laplaceAt F (s - (1 / 2 : Complex)) :=
  rfl

/-- The contour weight uses exactly the same centered transform as one
multiplicity-weighted spectral summand. -/
theorem spectralTerm_eq_multiplicity_mul_centeredLaplaceWeight
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    spectralTerm F rho =
      (xiMultiplicity rho : Complex) * centeredLaplaceWeight F rho.1 := by
  rfl

@[simp] theorem symmetrizedLaplaceWeight_one_sub
    (F : CompactLogTest) (s : Complex) :
    symmetrizedLaplaceWeight F (1 - s) =
      symmetrizedLaplaceWeight F s := by
  simp only [symmetrizedLaplaceWeight, sub_sub_cancel]
  exact add_comm _ _

/-- Differentiating `xi(1-s)=xi(s)` gives the required sign on the derivative.
This is the sign-sensitive bridge used by both vertical sides of the contour. -/
theorem deriv_completedRiemannXi_one_sub (s : Complex) :
    deriv completedRiemannXi (1 - s) =
      -deriv completedRiemannXi s := by
  have hinner : HasDerivAt (fun z : Complex => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : Complex)
  have hcomp :
      HasDerivAt (fun z : Complex => completedRiemannXi (1 - z))
        (-(deriv completedRiemannXi (1 - s))) s := by
    convert
      (differentiable_completedRiemannXi (1 - s)).hasDerivAt.comp s hinner using 1 <;>
      ring
  have hfunctions :
      (fun z : Complex => completedRiemannXi (1 - z)) =
        completedRiemannXi := by
    funext z
    exact completedRiemannXi_one_sub z
  have hderiv :
      deriv completedRiemannXi s =
        -(deriv completedRiemannXi (1 - s)) := by
    rw [hfunctions] at hcomp
    exact hcomp.deriv
  simpa only [neg_neg] using (congrArg Neg.neg hderiv).symm

/-- The xi logarithmic derivative is odd under the functional equation.  This
identity remains valid at zeros because Mathlib's `logDeriv` is total. -/
@[simp] theorem logDeriv_completedRiemannXi_one_sub (s : Complex) :
    logDeriv completedRiemannXi (1 - s) =
      -logDeriv completedRiemannXi s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_completedRiemannXi_one_sub,
    completedRiemannXi_one_sub]
  ring

@[simp] theorem negativeXiLogDeriv_one_sub (s : Complex) :
    negativeXiLogDeriv (1 - s) = -negativeXiLogDeriv s := by
  simp [negativeXiLogDeriv]

/-- The right-line kernel is odd under `s \mapsto 1-s`: the xi factor is
odd while the symmetrized test factor is even. -/
@[simp] theorem xiRightLineKernel_one_sub
    (F : CompactLogTest) (s : Complex) :
    xiRightLineKernel F (1 - s) = -xiRightLineKernel F s := by
  simp [xiRightLineKernel]

/-- The folded right-line kernel is the single kernel minus its reflected copy.
This is the algebraic form of the left-edge orientation reversal. -/
theorem xiRightLineKernel_eq_xiContourKernel_sub_reflected
    (F : CompactLogTest) (s : Complex) :
    xiRightLineKernel F s =
      xiContourKernel F s - xiContourKernel F (1 - s) := by
  simp only [xiRightLineKernel, xiContourKernel, symmetrizedLaplaceWeight,
    sub_eq_add_neg]
  have hreflect : negativeXiLogDeriv (1 + -s) = -negativeXiLogDeriv s := by
    convert negativeXiLogDeriv_one_sub s using 1 <;> ring
  rw [hreflect]
  rw [mul_add]
  ring

@[simp] theorem verticalPoint_reflection (c t : Real) :
    verticalPoint (1 - c) (-t) = 1 - verticalPoint c t := by
  apply Complex.ext <;> simp [verticalPoint] <;> ring

/-- Pointwise reflection of the two upward vertical-line integrands.  Reversing
the left side's orientation will therefore make the two rectangle sides add. -/
@[simp] theorem verticalIntegrand_reflection
    (F : CompactLogTest) (c t : Real) :
    verticalIntegrand F (1 - c) (-t) =
      -verticalIntegrand F c t := by
  rw [verticalIntegrand, verticalIntegrand, verticalPoint_reflection,
    xiRightLineKernel_one_sub]
  ring

end C1XiVerticalFunctional
end Source
end ConnesWeilRH
