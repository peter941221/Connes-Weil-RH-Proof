import ConnesWeilRH.Dev.ConcreteP1SupportProbe
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData

/-!
# L657 diagnostic (in progress) — clean concrete-carrier facts only

This leaf gathers, axiom-free, the concrete-carrier facts behind the L657 verdict
(`docs/proofs/923`): `archimedeanTerm = 0`, `globalPrimeIndexSet = {2}`,
`restrictedPrimeIndexSet 0 = empty`, and `IsPrimePow 2`.  These are the hinges of the
"`Common concreteW` is an empty type" diagnostic.  The on-`{2}` arithmetic-data
construction and the draining contradiction are WIP (separate leaf), deliberately
kept `sorry`-free here.

No RH claim.  Only the library trio axioms.
-/


namespace ConnesWeilRH
namespace Source
namespace Dev
namespace L657DiagnosticProbe
open ConcreteP1SupportProbe
open CCM25Concrete
open CCM25Concrete.PrimePowerArithmetic

/-- The axiom's concrete `W` is `toWeilFormSymbols` of `concreteWeilForm`. -/
noncomputable def Wconcrete : WeilFormSymbols :=
  ConcreteP1SupportProbe.concreteWeilForm.toWeilFormSymbols

/-- `archimedeanTerm` is definitionally `0` on the concrete carrier. -/
lemma archimedeanTerm_zero (F : TestFunction) :
    Wconcrete.archimedeanTerm F = 0 := by
  rfl

/-- The global prime index set is exactly `{2}`. -/
lemma global_index_set :
    Wconcrete.globalPrimeIndexSet = ({2} : Finset Nat) := by
  rfl

/-- The restricted prime index set at lambda=0 is empty. -/
lemma restricted_index_set_zero :
    Wconcrete.restrictedPrimeIndexSet 0 = (∅ : Finset Nat) := by
  unfold Wconcrete
  simp [concreteWeilForm, perCommonSupport]

/-- `IsPrimePow 2`: `2` is a prime power. -/
lemma two_is_prime_pow : IsPrimePow 2 :=
  Nat.prime_two.isPrimePow


end L657DiagnosticProbe
end Dev
end Source
end ConnesWeilRH
