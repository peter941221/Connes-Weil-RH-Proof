import ConnesWeilRH.Dev.Wall14PlateauIntegrateH
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open Filter Set
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner

/-! ### Near-band `(0, 1]` rotation-constant infrastructure

`g y = plateauArchG y = 2(e^{y/2} F(y) - A)/den y` with `den y = e^y - e^{-y}`,
`0 <= y`, and `F(0) = A`.  Because `F(0)=A` the numerator vanishes at `y=0`; a
slope control `|e^{y/2} F(y) - A| <= k*y` on `(0,1]` turns `|g| <= k` via
`den y >= 2*y` (the lemma below), after which `|integral_{(0,1]} g| <= k`.  The
`den y >= 2*y` record lives here (slope-free).  The slope control itself is the
surviving analytic leaf; mathlib's `ContDiffBump` (`plateauBump`) is opaque so a
pointwise F-slope needs the explicit-F re-point (docs/969).  RH NOT claimed.
-/

/-- `e^t + e^{-t} >= 2`, from `t+1 <= e^t` and `-t+1 <= e^{-t}`. -/
lemma exp_exp_le_ge_two (t : Real) : (2 : Real) <= Real.exp t + Real.exp (-t) := by
  have he1 : t + 1 <= Real.exp t := Real.add_one_le_exp t
  have he2 : -t + 1 <= Real.exp (-t) := Real.add_one_le_exp (-t)
  linarith

/-- `den y = e^y - e^{-y} >= 2*y` for `0 <= y`. -/
theorem deny_ge_two (y : Real) (hy : 0 <= y) : (2 : Real) * y <= den y := by
  let f : Real -> Real := fun y => den y - (2 : Real) * y
  have hf0 : f 0 = 0 := by
    simp [f, den, Real.exp_zero]
  have hder (x : Real) :
      HasDerivAt f (Real.exp x + Real.exp (-x) - (2 : Real)) x := by
    have hden : HasDerivAt (fun z : Real => den z) (Real.exp x + Real.exp (-x)) x := by
      simpa [den] using hasDerivAt_archimedeanDenominator x
    have htwo : HasDerivAt (fun z : Real => (2 : Real) * z) (2 : Real) x := by
      have hlin : HasDerivAt (fun z : Real => z * (2 : Real)) (2 : Real) x := by
        simpa using (hasDerivAt_id x).mul_const (2 : Real)
      simpa [mul_comm] using hlin
    simpa [f] using hden.sub htwo
  have hdiff : Differentiable Real f := by
    intro x
    exact (hder x).differentiableAt
  have hmono : Monotone f := monotone_of_deriv_nonneg hdiff (by
      intro x
      have hd : deriv f x = Real.exp x + Real.exp (-x) - (2 : Real) := (hder x).deriv
      rw [hd]
      exact sub_nonneg.mpr (exp_exp_le_ge_two x))
  have hle : f 0 <= f y := hmono hy
  have hfy : f y = den y - (2 : Real) * y := by rfl
  nlinarith [hf0, hfy, hle]

end Wall14Plateau
end Dev
end Source
end ConnesWeilRH