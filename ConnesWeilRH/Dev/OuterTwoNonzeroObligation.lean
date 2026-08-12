
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalLeakage
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationChannelSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCoframeResponse
import ConnesWeilRH.Source.CC20Concrete.CCM24EulerTransport

open scoped InnerProduct

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Source.CCM25Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSCoframeResponse

namespace ConnesWeilRH
namespace Dev
namespace OuterTwoNonzero

/-- The visible prime 2. -/
noncomputable def twoPrime : CCM24VisiblePrime :=
  { val := 2, property := by norm_num }

/-- The concrete nonempty family {2} (single prime-power term `2^1`). -/
noncomputable def twoFamily : FinitePrimePowerFamily where
  terms := {(2, 1)}
  prime := by
    intro pm hpm
    simp only [Finset.mem_singleton] at hpm
    rcases hpm with ⟨rfl, rfl⟩
    exact Nat.prime_two
  exponent_ne_zero := by
    intro pm hpm
    simp only [Finset.mem_singleton] at hpm
    rcases hpm with ⟨rfl, rfl⟩
    decide

/-- The {2} family contains the prime-power term 2^1. -/
lemma twoFamily_memTerm : (2, 1) ∈ twoFamily.terms := by
  simp [twoFamily]

/-- Obligation: the OUTER radial channel is nonzero on the {2} family.
This is docs/998; declaring the Prop asserts no proof and no axiom. -/
noncomputable def twoOuterNonzeroObligation (lambda : CCM24SoninScale) : Prop :=
  sourceOuterCoframeLeakage lambda twoFamily ≠ 0

end OuterTwoNonzero
end Dev
end ConnesWeilRH
