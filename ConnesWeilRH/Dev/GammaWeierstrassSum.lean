import ConnesWeilRH.Dev.GammaArgProd
import ConnesWeilRH.Dev.SSeriesSandwich
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

end GammaWeierstrassSum
end Dev
end ConnesWeilRH
