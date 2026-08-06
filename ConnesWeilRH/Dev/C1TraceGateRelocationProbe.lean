/-
C1 probe (route-C relocation / idea C): SEPARATE the formal trace-class closure
from the analytic carrier question.  The decisive finding, by building: the
"relocation lemma" 826 wanted is ALREADY a theorem in
`GlobalLogCrossingTraceClass.lean`.  `cc20SmoothedCrossing b k h` is an H→H
operator on the crossing space (a rank-one smoothing), and
`..._positiveComposition_trace_nonnegative` proves

    0 ≤ (ordinaryTraceAlong basis (positiveComposition data)).re

for ARBITRARY carriers `k h`.  So the formal nonnegativity of the Gate scalar is
already proven, axiom-free, with NO new math and NO dependence on Proof-717's
operator-norm wall.  The ONLY analytic input C still needs is a NONZERO carrier
`k` making the trace genuinely informative (not the zero scalar).

This probe does three things, all zero-new-math:
  1. States the relocation lemma in the strongest already-proved form
     (any carrier -> positive trace), citing the library theorem.
  2. Proves the trace has an explicit inner-product VALUE (`= ⟪h, SingleCrossing b k⟫`),
     already in-library.  This is the scalar the gate must bound.
  3. Honesty: two concrete provable facts are stated.  The ANALYTIC residue --
     existence of a NONZERO carrier k with `⟪h, SingleCross b k⟫ ≠ 0` (the A0 gap) --
     is NOT claimed here; it is the exact parallel of A3's `nonzero_hsGate_witness`.
     Nothing claims RH.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossingTraceClass
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1TraceGateRelocationProbe

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open PositiveTrace

noncomputable abbrev Crossing := cc20GlobalLogCrossingL2

/--
RELOCATION, STRONG FORM (zero-new-math assembly; cites the in-library theorem):
for ANY carrier vectors `k h : Crossing` and any Hilbert basis, the positive
composition trace of the rank-one smoothing is a real nonnegative scalar.  This
is the entire "formal closure" of the trace-side Gate; it needs no operator-norm
comparison and no A0-prime closure.  It is literally the library lemma restated.
-/
theorem traceGate_formallyClosed_anyCarrier
    (b : ℝ) (k h : Crossing) {ι : Type*}
    (basis : HilbertBasis ι ℂ Crossing) :
    0 ≤ (ordinaryTraceAlong basis
      (cc20SmoothedCrossingBasisHilbertSchmidtData b k h basis).positiveComposition).re :=
  cc20SmoothedCrossing_positiveComposition_trace_nonnegative b k h basis

/--
The explicit VALUE form: `Tr = ⟪h, singleCrossing b k⟫`.  So the Gate scalar is
exactly that inner product; bounding it to the majorant is equivalent to bounding
this contraction, NOT to a Proof-717 norm identity.  This is the trace-side
readout C replaces the metric-norm readout with.
-/
theorem relocationGate_scalar_innerForm
    (b : ℝ) (k h : Crossing) {ι : Type*}
    (basis : HilbertBasis ι ℂ Crossing) :
    ordinaryTraceAlong basis (cc20SmoothedCrossing b k h) =
      ⟪h, cc20SingleCrossingOperator b k⟫_ℂ :=
  cc20SmoothedCrossing_ordinaryTraceAlong b k h basis

end C1TraceGateRelocationProbe
end Dev
end Source
end ConnesWeilRH