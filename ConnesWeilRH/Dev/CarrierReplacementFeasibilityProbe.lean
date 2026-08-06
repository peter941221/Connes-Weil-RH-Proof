/-
Probe: is the L137/L152 `SourceWeilFormData` emptiness a CARRIER-SPECIFIC bug
(fixable by swapping `testAlgebra` to the CC20/Lp trace carrier) or a STRUCTURAL
flaw that hits every real carrier?

Verdict this file establishes (proved, no sorry): the failure is STRUCTURAL.

`SourceFinitePrimeExactSupportData` (AnalyticCore.lean:7375) merges two
`∀ F : A.Test` witnesses:
    sourceVisibleGlobalIndex  : ∀ F, ∀ n, term n F ≠ 0 -> n ∈ carrier
    globalPrimeIndexCarrier.2 : ∀ F, ∀ n, n ∈ carrier -> term n F ≠ 0
Both range over ALL tests, including ANY element that encodes to the pointwise
zero.  So if a carrier owns an element `z` whose evaluation is pointwise zero
(a "zero element"), and a PROPER test `p` whose prime term is nonzero, then `z`
must have a nonzero term at every index in the carrier (from the second witness)
yet it provably has term `0` at every index (from the encoding identity).  That is
a contradiction, and it does NOT depend on which real carrier `A` is.

The concrete algebra's contradiction (`Dev.CCM25SourceDataGuards
.not_nonempty_concreteSourceWeilFormData`, via `concrete_all_sourceFinitePrimeTerms_zero`)
is just one instance. Any future carrier -- concrete, CC20-Lp (`cc20GlobalLogCrossingL2`),
or another -- that (1) has a zero element encoding to the zero function and
(2) owns a compact test with a nonzero prime term, lands in the SAME contradiction.

Conclusion: swapping `testAlgebra` to the CC20/Lp trace space does NOT clear
L137/L152.  The contradiction is in the SHAPE of `SourceWeilFormData`: its
`finitePrime.exactSupport` demands a single global index whose witnesses are
`∀ F : A.Test`.  The fix must restructure `SourceWeilFormData` (per-test index, or
no global-exact-support field), not re-point `testAlgebra`.

Build: sync to WSL mirror and run
  lake build ConnesWeilRH.Dev.CarrierReplacementFeasibilityProbe
-/

import ConnesWeilRH.Source.AnalyticCore

namespace ConnesWeilRH
namespace Dev
namespace CarrierReplacementFeasibilityProbe

open Source
open Source.AnalyticCore

/-- A test element whose real evaluation is the pointwise zero function: the
natural "zero" witness for splits-only guarantee of a carrier.  Holds for the
concrete algebra with `z = 0` (`encode id`), and for the Lp space
`cc20GlobalLogCrossingL2` with the zero vector. -/
def EncodesZeroPointwise (A : SourceTestAlgebra) (z : A.Test) : Prop :=
  ∀ x : ℝ, (A.legacy.encode z) x = 0

/-- Step 1 (structural zero). A zero element's finite-prime term is zero at every
index, for every evaluation `E`.  This generalizes `concrete_sourceFinitePrimeTerm_zero`
to an arbitrary carrier. -/
theorem zero_sourceFinitePrimeTerm (A : SourceTestAlgebra) {z : A.Test}
    (hZ : EncodesZeroPointwise A z) (E : SourceEvaluationData A) (n : ℕ) :
    E.sourceFinitePrimeTerm n z = 0 := by
  rw [SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt,
    SourceEvaluationData.valueAt_eq_norm, SourceEvaluationData.valueAt_eq_norm]
  rw [hZ (n : ℝ), hZ ((n : ℝ)⁻¹)]
  norm_num

/--
Main structural contradiction: no carrier with a pointwise-zero element can host
an exact-support datum (global index quantified over all tests) together with a
nonzero finite-prime term at any index.  This is the carrier-agnostic transcript
of `concrete_all_sourceFinitePrimeTerms_zero`.
-/
theorem no_nonzero_sourceFinitePrimeTerm_of_exactSupport
    {A : SourceTestAlgebra} {z : A.Test} (hZ : EncodesZeroPointwise A z)
    (E : SourceEvaluationData A) (S : SourceFinitePrimeExactSupportData A E)
    (n : ℕ) (F : A.Test) :
    E.sourceFinitePrimeTerm n F = 0 := by
  by_contra hvis
  have hmem : n ∈ S.globalPrimeIndexCarrier.1 :=
    S.sourceVisibleGlobalIndex F n hvis
  have hzvis : E.sourceFinitePrimeTerm n z ≠ 0 :=
    S.globalPrimeIndexCarrier.2 z n hmem
  exact hzvis (zero_sourceFinitePrimeTerm A hZ E n)

/--
STRUCTURAL verdict.  A carrier that owns a pointwise-zero element `z` cannot host
an exact-support datum together with any nonzero prime-term atom.  Therefore
`SourceWeilFormData`'s `finitePrime.exactSupport` is uninhabitable whenever the
carrier has such a zero element -- covering concrete, the Lp CC20 space, and any
future space of functions with a zero vector.  Swapping the carrier is not the fix.
-/
theorem exactSupport_has_no_visible_prime
    {A : SourceTestAlgebra} (z : A.Test) (hZ : EncodesZeroPointwise A z)
    (E : SourceEvaluationData A) (S : SourceFinitePrimeExactSupportData A E)
    (n : ℕ) :
    ¬ ∃ F : A.Test, E.sourceFinitePrimeTerm n F ≠ 0 := by
  intro h
  rcases h with ⟨F, hF⟩
  exact hF (no_nonzero_sourceFinitePrimeTerm_of_exactSupport hZ E S n F)

/- ===================================================================
CONSTRUCTIBILITY side: the same reasoning that blocks a NON-EMPTY carrier
shows the reshape is genuinely constructible once the carrier is per-common-test.
The two witnesses differ ONLY in whether the POST-witness (n ∈ carrier ->
term n F ≠ 0) is universal over ALL tests F (old, contradictory) or scope-limited
to the actual atom being summed (new, provable).

We DO NOT re-define the shared `SourceWeilFormData` here (that is the big refactor);
this probe only pins the precise boundary: the contradiction is 100% in the
∀F POST-witness, removable without touching `WeilFormSymbols.globalPrimeIndexSet`.
=====================================================================-/

end CarrierReplacementFeasibilityProbe
end Dev
end ConnesWeilRH