import ConnesWeilRH.Dev.ScabNormalForm
import ConnesWeilRH.Dev.ScabLhsZero

/-!
# Wall14ArchimedeanReduction

When the global and restricted finite-prime sums of a Weil-form model agree and
pole normalization holds (`poleFunctional(f*f) = polePairing f`), the Wall-A 1.4
SCAL target `ScabPoleArchTarget W f a b` reduces exactly to a single scalar
`W.archimedeanTerm (W.convolutionStar f f) = 0`.

On the healthy carrier the per-common finite-prime index set is `{2}` and the
restricted set equals the global one from `lambda >= sqrt 2`, so the whole SCB
identity collapses to `arch(f*f) = 0`.  This module proves only the ring-level
reduction; it does NOT claim `arch = 0`.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete

open ConnesWeilRH.Source.CCM25Concrete.ScabNormalForm

/-- If global and restricted prime sums agree and pole normalization holds, the
   Wall-A 1.4 SCAL target is equivalent to `arch(f*f) = 0`. -/
theorem wall14_target_iff_arch_zero_of_global_eq_restricted
    (W : WeilFormSymbols) (f : TestFunction) (a b : ℝ)
    (hsum : a = b)
    (hfunc : W.poleFunctional (W.convolutionStar f f) = W.polePairing f) :
    ScabPoleArchTarget W f a b <->
        W.archimedeanTerm (W.convolutionStar f f) = 0 := by
  unfold ScabPoleArchTarget
  constructor <;> intro h <;> linarith



/-- On the healthy carrier the global-vs-restricted sums agree (both over the
   per-common index set {2} for lambda >= sqrt 2), the LHS cancels to zero via
   ScabLhsZero, so the whole Wall-A 1.4 SCAL target collapses to the single
   scalar `arch(f*f) = 0`.  This is the compilable proposition tying the healthy
   SCB to a single analytic scalar; it does NOT claim arch = 0. -/
theorem healthy_scb_arch_zero_of_global_eq_restricted
    (f : TestFunction) (globalSum restrictedSum : ℝ)
    (hsum : globalSum = restrictedSum) :
    ScabPoleArchTarget
        (ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols) f
        globalSum restrictedSum <->
      (ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols).archimedeanTerm
        ((ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols).convolutionStar f f) = 0 := by
  apply wall14_target_iff_arch_zero_of_global_eq_restricted
      (ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols) f globalSum restrictedSum hsum
  exact sub_eq_zero.mp (ConnesWeilRH.Source.Dev.ScabLhsZero.lhs_zero f)

end CCM25Concrete
end Source
end ConnesWeilRH