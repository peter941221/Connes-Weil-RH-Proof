import ConnesWeilRH.Dev.GammaArgProd
import ConnesWeilRH.Dev.SSeriesSandwich
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
/-!
# GammaWeierstrassSum: finite product-angle partial sums (docs/941, Step-3)

Ties the finite Weierstrass-factor product angle (GammaArgProd) to the
`SSeriesSandwich` partial sums: with `u = n+1` the per-factor argument
`weylArgNum (n+1) = -1/(2(n+1)) + atan(1/(2(n+2)))`, and the Lean series
`SSandwich.a n = 1/(2(n+1)) - atan(1/(2(n+2)))`, so the angle of the finite
product over `range N` is `-` the corresponding partial sum of `a`.

This is the finite (angle) preimage of
`arg(Gamma(1+I/2)) = -gamma/2 - atan(1/2) + tsum a`; the `-1/2 - atan` core and
the Gamma-integral side remain the open Weierstrass / infinite-log-Gamma hinge
(docs/940). axiom-clean off mathlib foundations.
-/
namespace ConnesWeilRH
namespace Dev
namespace GammaWeierstrassSum

/- The per-factor argument at scale `u = n+1` is the negative of the `a`-series. -/
theorem weylArgNum_eq_neg_a (n : Nat) :
    WeierstrassFactorArg.weylArgNum (n + 1) =
      -ConnesWeilRH.Source.Dev.SSandwich.a n := by
  unfold WeierstrassFactorArg.weylArgNum ConnesWeilRH.Source.Dev.SSandwich.a
  ring_nf

/- The partial sums of the per-factor arguments equal the negative partial sum of
the closed `a`-series: `angle_1..N = sum_{n<N} weylArgNum(n+1) = -sum_{n<N} a n`. -/
theorem weylArgNum_range_eq_neg_sum (N : Nat) :
    (Finset.sum (Finset.range N) (fun n : Nat => WeierstrassFactorArg.weylArgNum (n + 1)))
      = -(Finset.sum (Finset.range N) fun n => ConnesWeilRH.Source.Dev.SSandwich.a n) := by
  calc
    (Finset.sum (Finset.range N) (fun n : Nat => WeierstrassFactorArg.weylArgNum (n + 1)))
        = Finset.sum (Finset.range N) (fun n : Nat => -ConnesWeilRH.Source.Dev.SSandwich.a n) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact weylArgNum_eq_neg_a n
    _ = -(Finset.sum (Finset.range N) fun n => ConnesWeilRH.Source.Dev.SSandwich.a n) :=
          by rw [Finset.sum_neg_distrib]



/- The per-factor argument sequence converges (in `Real`) to `-S`, the negative
of the closed `S`-series sum; this is the limit the Weierstrass log-Gamma phase
hinge (docs/940) needs on its series side. -/
theorem hasSum_weylArgNum :
    HasSum (fun n : Nat => WeierstrassFactorArg.weylArgNum (n + 1))
      (-ConnesWeilRH.Source.Dev.SSandwich.S) := by
  have hf : (fun n : Nat => WeierstrassFactorArg.weylArgNum (n + 1)) =
      fun n : Nat => -ConnesWeilRH.Source.Dev.SSandwich.a n := by
    funext n
    exact weylArgNum_eq_neg_a n
  rw [hf]
  exact HasSum.neg ConnesWeilRH.Source.Dev.SSandwich.a_summable.hasSum

/- Numeric bracket on the phase partial sum, from the closed S sandwich: -/
theorem negS_bounds :
    - (1 / 2 : Real) - 1 / 32 <= -ConnesWeilRH.Source.Dev.SSandwich.S ∧
      -ConnesWeilRH.Source.Dev.SSandwich.S <= - (1 / 2 : Real) := by
  constructor
  · have hS := ConnesWeilRH.Source.Dev.SSandwich.S_le_half_plus
    linarith
  · have hS := ConnesWeilRH.Source.Dev.SSandwich.S_ge_half
    linarith

/- The `Real.Angle`-valued Weierstrass phase series converges to `(-S : Real.Angle)`,
the image of the real `HasSum` under the continuous angle quotient. This is the
infinite-product-angle value the Gamma hinge (docs/940) needs on its product side. -/
theorem hasSum_angle_weylArg :
    HasSum (fun n : Nat => ((WeierstrassFactorArg.weylArgNum (n + 1)) : Real.Angle))
      ((-ConnesWeilRH.Source.Dev.SSandwich.S : Real) : Real.Angle) := by
  have h := hasSum_weylArgNum.map Real.Angle.coeHom Real.Angle.continuous_coe
  simpa [Real.Angle.coe_coeHom] using h
end GammaWeierstrassSum
end Dev
end ConnesWeilRH