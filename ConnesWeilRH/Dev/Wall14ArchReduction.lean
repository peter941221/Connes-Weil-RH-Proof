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



/-- The healthy carrier Wall-A 1.4 balanced target is refuted whenever the
   archimedean term is non-zero: `arch(f*f) != 0` forces the SCB balance to
   fail as a true statement.  This is the formal hinge through the healthy
   reduction; the analytic input `arch(f*f) != 0` (positive Eq.3.7 coefficient
   + docs/958 probe) is the open bottom that decides the dead/not verdict. -/
theorem healthy_target_refuted_of_arch_ne_zero
    (f : TestFunction) (globalSum restrictedSum : Real)
    (hsum : globalSum = restrictedSum)
    (harch : Not ((ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols).archimedeanTerm
        ((ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols).convolutionStar f f) = 0)) :
    Not (ScabPoleArchTarget
        (ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols) f
        globalSum restrictedSum) := by
  intro htarget
  have heq : (ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols).archimedeanTerm
        ((ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols).convolutionStar f f) = 0 :=
      (healthy_scb_arch_zero_of_global_eq_restricted f globalSum restrictedSum hsum).mp htarget
  exact harch heq

end CCM25Concrete
end Source
end ConnesWeilRH