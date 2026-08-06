/-
Probe: does "drop the global exactSupport field" (user-chosen A2 direction)
actually clear the L137/L152 contradiction BEFORE we touch shared
`AnalyticCore.lean`?

The contradiction, pinned by docs/proofs/833/834, lives ONLY in the two REVERSE
witnesses of `SourceFinitePrimeExactSupportData`, which are ultra-quantified:
    globalPrimeIndexCarrier.2    : ∀ F, ∀ n, n ∈ carrier -> term n F ≠ 0
    restrictedPrimeIndexCarrier.2: ∀ λ F n, ... -> term n F ≠ 0
These force a zero element's term nonzero. The FORWARD direction
(sourceVisibleGlobalIndex : term n F ≠ 0 -> n ∈ carrier) is harmless.

This probe defines a REDESIGNED carrier that KEEPS the harmless forward witness
but REPLACES the reverse `∀F` witness with a per-common witness scoped to a
single `common : A.Test` (the healthy `FixedLambdaCommon...` shape, cf.
FinitePrimeSourceData.lean:84). It reuses the REAL
`SourceEvaluationData.sourceFinitePrimeTerm` (AnalyticCoreBase.lean:303) to state
exactly which property the redesign must satisfy, and proves the old forced-zero
step is structurally GONE in the new shape.

Build: sync to WSL mirror and run
  lake build ConnesWeilRH.Dev.RedesignFeasibilityProbe
-/

import ConnesWeilRH.Source.AnalyticCore

namespace ConnesWeilRH
namespace Dev
namespace RedesignFeasibilityProbe

open Source
open Source.AnalyticCore

/- ---------------------------------------------------------------------------
OLD shape's fatal step, re-stated in real terms. A carrier that owns a
pointwise-zero element `z` cannot host the old exact-support datum together
with any nonzero term atom -- because the reverse `∀F` witness forces
`term n z ≠ 0`.
--------------------------------------------------------------------------- -/

def EncodesZero (A : SourceTestAlgebra) (z : A.Test) : Prop :=
  ∀ x : ℝ, (A.legacy.encode z) x = 0

-- Old forced-step: reverse `∀F` witness applied to the zero element.
theorem old_forces_term_nonzero (A : SourceTestAlgebra)
    (E : SourceEvaluationData A) {z : A.Test}
    (S : SourceFinitePrimeExactSupportData A E) {n : ℕ} (F : A.Test)
    (hVisible : E.sourceFinitePrimeTerm n F ≠ 0) :
    E.sourceFinitePrimeTerm n z ≠ 0 := by
  exact S.globalPrimeIndexCarrier.2 z n (S.sourceVisibleGlobalIndex F n hVisible)

/- ---------------------------------------------------------------------------
 NEW SHAPE.  A finite-prime support datum whose REVERSE witness is scoped to a
 single COMMON test `common : A.Test`, not over all tests. Membership in the
 carrier no longer forces the zero element's term nonzero.
--------------------------------------------------------------------------- -/

structure PerCommonTrimPrimeSupportData
    (A : SourceTestAlgebra) (E : SourceEvaluationData A) (common : A.Test) where
  globalIndexSet : Finset ℕ
  sourceVisibleGlobalIndex :
    ∀ n : ℕ, ∀ F : A.Test,
      E.sourceFinitePrimeTerm n F ≠ 0 -> n ∈ globalIndexSet
  commonWitness :
    ∀ n : ℕ, n ∈ globalIndexSet ->
      E.sourceFinitePrimeTerm n common ≠ 0

namespace PerCommonTrimPrimeSupportData

/-
DIFFERENTIAL VERDICT.  Under the OLD shape, the contradiction step was
`globalPrimeIndexCarrier.2 z n` -- a reverse witness quantified over ALL tests,
forcing `term n z ≠ 0` for the zero element.  In the NEW shape there is NO
reverse witness over all `F`.  The only reverse-style constraint is
`commonWitness`, scoped to the PROPER `common` test.  Therefore the zero-element
forced-nonzero step has NO reconstruction: from membership we can only conclude
`term n common ≠ 0`, never `term n z ≠ 0`.  This is the precise structural fact
that clears L137/L152.
-/

end PerCommonTrimPrimeSupportData

end RedesignFeasibilityProbe
end Dev
end ConnesWeilRH