import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData

/-!
# ScabNormalForm — SCB normal form: the global-vs-restricted balance reduces
to a single pole/arch scalar target

`SourceScopedArchimedeanContributionBalance` (SCB, FinitePrimeSourceData) states
`restricted = global`, where

    restricted = arch(f*f) + polePairing(f) - restrictedSum
    global     = poleFunctional(f*f) - arch(f*f) - globalSum

This module gives the *algebraic normal form* of that statement: it strips the
cancelling copy of `arch(f*f)` and reduces the whole SCB to the single scalar
identity

    poleFunctional(f*f) - polePairing(f) = 2*arch(f*f) + (globalSum - restrictedSum)

which is exactly the WEIL-EXPLICIT-FORMULA content (Wall-A sub-step 1.4).
Everything here is ring/`linarith`; it does NOT prove the analytic identity, it
pins down the precise scalar equality a real analytic proof must establish.
RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace ScabNormalForm

open FinitePrimeSourceData

/-- The named target of the SCB: the single pole/arch scalar identity whose
proof would close the global-vs-restricted balance. -/
def ScabPoleArchTarget
    (W : WeilFormSymbols) (f : TestFunction)
    (globalSum restrictedSum : ℝ) : Prop :=
  W.poleFunctional (W.convolutionStar f f) - W.polePairing f =
    2 * W.archimedeanTerm (W.convolutionStar f f) +
      (globalSum - restrictedSum)

/-- The two SCAB sides reduce to the single pole/arch scalar target; i.e. the
   balance is *equivalent* to the explicit-formula identity above. -/
theorem scab_iff_pole_arch_target
    (W : WeilFormSymbols) (f : TestFunction)
    (globalSum restrictedSum : ℝ) :
    (W.archimedeanTerm (W.convolutionStar f f) + W.polePairing f - restrictedSum =
        W.poleFunctional (W.convolutionStar f f) -
          W.archimedeanTerm (W.convolutionStar f f) - globalSum)
      ↔ ScabPoleArchTarget W f globalSum restrictedSum := by
  unfold ScabPoleArchTarget
  constructor <;> intro h <;> linarith

end ScabNormalForm
end CCM25Concrete
end Source
end ConnesWeilRH