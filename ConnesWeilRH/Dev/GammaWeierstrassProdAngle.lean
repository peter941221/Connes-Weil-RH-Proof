import ConnesWeilRH.Dev.GammaArgProd
import ConnesWeilRH.Dev.GammaArgSum
import ConnesWeilRH.Dev.GammaWeierstrassSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# GammaWeierstrassProdAngle: infinite-product angle spine (docs/941)

Closes the PRODUCT side of the Weierstrass-phase hinge: the argument (as
Real.Angle) of the finite Weierstrass partial product over scales u = 1 + i
(converges to the closed series value (-S) as N → infinity.
-/
open Filter

namespace ConnesWeilRH
namespace Dev
namespace GammaWeierstrassProdAngle

/-- finite Weierstrass partial product over scales u = 1 + i. -/
noncomputable def partialProduct (N : Nat) : Complex :=
  Finset.prod (Finset.range N) (fun n : Nat =>
    WeierstrassFactorArg.weylFactor ((n + 1 : Nat) : Real))

theorem partialProduct_arg_eq_angle_sum (N : Nat) :
    ((partialProduct N).arg : Real.Angle)
      = Finset.sum (Finset.range N) (fun n : Nat =>
          (WeierstrassFactorArg.weylArgNum (n + 1 : Nat) : Real.Angle)) := by
  dsimp [partialProduct]
  classical
  have hnonzero : ∀ i : Nat, i ∈ Finset.range N →
      WeierstrassFactorArg.weylFactor ((i + 1 : Nat) : Real) ≠ 0 := by
    intro i _
    exact WeierstrassFactorArg.weylFactor_ne_zero ((i + 1 : Nat) : Real)
      (by positivity)
  rw [GammaArgSum.arg_prod_coe_angle (t := Finset.range N)
      (f := fun n : Nat => WeierstrassFactorArg.weylFactor ((n + 1 : Nat) : Real))
      hnonzero]
  rw [GammaArgSum.real_sum_coe_angle (Finset.range N)
      (fun n : Nat => (WeierstrassFactorArg.weylFactor ((n + 1 : Nat) : Real)).arg)]
  apply Finset.sum_congr rfl
  intro n _
  simpa [WeierstrassFactorArg.weylArgNum] using
    WeierstrassFactorArg.arg_weylFactor ((n + 1 : Nat) : Real) (by positivity)

theorem tendsto_product_angle_arg :
    Tendsto (fun N : Nat => ((partialProduct N).arg : Real.Angle))
      atTop (nhds ((-ConnesWeilRH.Source.Dev.SSandwich.S : Real) : Real.Angle)) := by
  let g : Nat -> Real.Angle := fun N =>
    Finset.sum (Finset.range N) (fun n : Nat =>
      (WeierstrassFactorArg.weylArgNum (n + 1 : Nat) : Real.Angle))
  have heq : (fun N : Nat => ((partialProduct N).arg : Real.Angle)) = g := by
    funext N
    simpa [g] using partialProduct_arg_eq_angle_sum (N := N)
  rw [heq]
  simpa [g] using GammaWeierstrassSum.hasSum_angle_weylArg.tendsto_sum_nat
end GammaWeierstrassProdAngle
end Dev
end ConnesWeilRH

