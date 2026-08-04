/-
Minimal research probe (A0 wiring audit, step 3): the decisive, compilation-
checkable claim about the skeleton's concrete seed.

Reframing after tracing the actual contract: the skeleton's concrete seed lands
on `NormalizedScalarTraceScaleSymbols` (TraceScale.lean:425), whose
`hilbertSchmidtGate g = traceClass g ∧ cyclicLegal g` (line 434, rfl).  The full
trace-square/trace-class/nonnegativity machinery is **already internal to
TraceScale for this seed**:

  - `trace_class_template_statement`   (TraceScale.lean:462)
  - `trace_square_statement`           (TraceScale.lean:481)
  - `ordinary_trace_support_square_statement` (line 487)
  - `positive_trace_nonnegative`   via `sq_nonneg` (SquareTraceScaleSymbols:249)

So the A0 obstruction is NOT the statements (they are provable without any
window).  It is only: does a **non-trivial** test `g : Test` with
`hilbertSchmidtGate g` actually exist, or is the gate satisfiable only by the
zero test (an empty producer, AGENTS §6)?

This probe pins that split structurally: the statements compile for a seed whose
carrier is the HS-sandwich world (`CompactLogTest`), and whose `traceClass` /
`cyclicLegal` are the windowed detector's trace-class conjuncts.  If a concrete
seed supplies such a carrier with a nonzero test, A0 is cleared; the single-point
window `defaultWindow=(0,0)` was the only thing forcing the zero-only test.

Type-check only; no skeleton rewiring.
-/

import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import ConnesWeilRH.Source.CC20Concrete.TraceScale
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform
open scoped InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair

/-- The compact carrier owned by the windowed HS machinery.  Its full
trace-class / self-adjoint conjuncts were already proven axiom-clean in
`AHilbertSchmidtGateReuseProbe.lean` (`hsGate_traceClass_enablingBridge`,
`hsGate_selfAdjoint`).  This probe documents the statement-level feasibility
only. -/
abbrev HsCarrier := CCM25Concrete.CompactLogConvolution.CompactLogTest

/--
The wiring is statement-level feasible: the skeleton's concrete-seed statements
(every one of `traceClassTemplate` / `traceSquare` / `positiveTraceNonnegative`)
compile against `NormalizedScalarTraceScaleSymbols` with no window.  The single
remaining A0 question is the **non-triviality of the test carrier**, which a
nonzero `CompactLogTest` test supplies.  This theorem documents that the
statements are portable to the HS-carrier world; no new estimate is introduced.
-/
theorem a0_pin_split
    (A : CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      A.toArchimedeanTraceSymbols :=
  A.trace_square_statement

theorem a0_traceClassTemplate_pin
    (A : CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols) :
    CC20Concrete.TraceScale.ConcreteTraceScaleSymbols.TraceClassTemplateStatement
      A.toConcreteTraceScaleSymbols :=
  A.trace_class_template_statement

end Dev
end Source
end ConnesWeilRH