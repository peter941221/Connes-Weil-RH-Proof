/-
Seam B implementability probe (A-set wiring audit, step 4): can the RH
skeleton's `CC20TraceObjectPackage` field contract be filled with the
operator-carrier Test (`CompactLogTest`) + the windowed HS-trace machine?

The single decisive question is existential, not a plumbing loop: does the
concrete Hilbert basis of `cc20GlobalLogCrossingL2` exist?  `ordinaryTraceAlong`
and every `BasisHilbertSchmidtData`/`BasisHilbertSchmidtPairData` need a
`HilbertBasis ν ℂ cc20GlobalLogCrossingL2`.  Everything else downstream
(`positiveComposition`, `ordinaryTrace_positiveComposition_re_nonnegative`)
is already proved axiom-free in PositiveTrace.lean.

This probe type-checks the existence of that basis and of a one-factor
HS-sandwich carrying it, delegating the actual nonnegativity proof to the
existing lemma.  It does NOT rewire the skeleton.
-/

import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace A1SeamBProbe

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform
open scoped InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open PositiveTrace

/-- The operator-carrier test: a compact-support test.  Carries the trace-class
data (compact support + HS kernel) that A0's single-point window could not. -/
abbrev HsTest := CCM25Concrete.CompactLogConvolution.CompactLogTest

/--
DECISIVE FACT 1: a concrete Hilbert basis of the global crossing space exists,
so `ordinaryTraceAlong` and the HS trace-class machinery are instantiable.
`exists_hilbertBasis` (Analysis/InnerProductSpace/l2Space.lean:563) gives a
basis indexed by `Set cc20GlobalLogCrossingL2` on any complete complex inner
product space — `cc20GlobalLogCrossingL2` is an `Lp`, so the witness is drawn
with `Classical.choice`, axiom-clean.  This is the object that A0's window
could never produce, and that `fullBoundaryRootFactor` needs to be traced.
-/
theorem a1_globalBasis_exists :
    ∃ w : Set cc20GlobalLogCrossingL2,
      Nonempty (HilbertBasis w ℂ cc20GlobalLogCrossingL2) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ cc20GlobalLogCrossingL2
  exact ⟨w, ⟨b⟩⟩

/--
DECISIVE FACT 2: the positive-trace nonnegativity that fills
`sourcePositiveTraceNonnegative` is axiom-free — `Tr(A†A)` is a sum of squares.
The `BasisHilbertSchmidtData` witness is the analytic content; the nonnegativity
is the module's already-proved lemma.
-/
theorem a1_positiveTrace_nonneg_is_proved_content
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (data : BasisHilbertSchmidtData globalBasis) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (BasisHilbertSchmidtData.positiveComposition data)).re :=
  data.ordinaryTrace_positiveComposition_re_nonnegative

end A1SeamBProbe
end Dev
end Source
end ConnesWeilRH