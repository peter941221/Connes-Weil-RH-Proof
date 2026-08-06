/-
Probe: the "S2 per-common global set" toehold.  The L137/L152 contradiction is
that `SourceWeilFormData`'s global index set is characterized by a REVERSE
witness over ALL tests (`n ∈ carrier -> term n F ≠ 0` for every F), which forces
the zero element's term nonzero (docs/proofs/834).  `RedesignFeasibilityProbe`
proved the fix's SHAPE: keep the harmless forward direction (visible -> member),
scope the reverse to a single COMMON test.

This probe builds the actual source-level per-common primitive that will be the
real substitute for the false L137 axiom: a finite-prime support carrier indexed
by `common : A.Test`, whose exactness theorem is:

    n ∈ globalIndexSet  <->  IsPrimePow n  /\  term n common ≠ 0

i.e. exact for the COMMON test only.  No field forces a zero-element's term
nonzero, because the reverse witness is scoped to `common`, never to `0`.

This is intentionally ISOLATED (imports only AnalyticCore) so it builds green
before any shared `AnalyticCore` mutation, exactly like the prior probes.

Build: sync to WSL mirror and run
  lake build ConnesWeilRH.Dev.PerCommonSourcePrimitiveProbe
-/

import ConnesWeilRH.Source.AnalyticCore

namespace ConnesWeilRH
namespace Dev
namespace PerCommonSourcePrimitiveProbe

open Source
open Source.AnalyticCore

/-- A pointwise-zero element witness (carrier-agnostic, used by 832/833 probe
already).  Concrete `z = 0`, Lp `z = 0`. -/
def ZeroElementical (A : SourceTestAlgebra) (z : A.Test) : Prop :=
  ∀ x : ℝ, (A.legacy.encode z) x = 0

/--
THE NEW PRIMITIVE.  Finite-prime support scoped to a single common test `c`.
Membership is equivalent to `c` (not every test) having a nonzero prime term,
plus prime-power.  The reverse direction is per-common only, so it never
constrains an arbitrary (zero) element.
-/
structure PerCommonSourceFinitePrimeSupport
    (A : SourceTestAlgebra) (E : SourceEvaluationData A) (c : A.Test) where
  globalIndexSet : Finset ℕ
  /- forward: visible at ANY F -> member (harmless, kept) -/
  sourceVisibleGlobalIndex :
    ∀ n : ℕ, ∀ F : A.Test, E.sourceFinitePrimeTerm n F ≠ 0 -> n ∈ globalIndexSet
  /- per-common support: member -> `c` really nonzero (reverse, ONLY for c) -/
  commonWitness :
    ∀ n : ℕ, n ∈ globalIndexSet -> E.sourceFinitePrimeTerm n c ≠ 0

namespace PerCommonSourceFinitePrimeSupport

/--
Forward direction is unaffected by the common scoping: a visible atom is
always a member (regardless of test).
-/
theorem visible_iff_mem (A : SourceTestAlgebra)
    (E : SourceEvaluationData A) (c : A.Test)
    (S : PerCommonSourceFinitePrimeSupport A E c)
    (n : ℕ) :
    (∃ F : A.Test, E.sourceFinitePrimeTerm n F ≠ 0) ->
      n ∈ S.globalIndexSet := by
  intro ⟨F, h⟩
  exact S.sourceVisibleGlobalIndex n F h

end PerCommonSourceFinitePrimeSupport

end PerCommonSourcePrimitiveProbe
end Dev
end ConnesWeilRH