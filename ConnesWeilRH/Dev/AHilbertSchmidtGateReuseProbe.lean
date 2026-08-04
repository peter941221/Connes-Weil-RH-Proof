/-
Minimal research probe: does the existing windowed HS-trace machinery
(`CompactRootHalfLinePair`) already supply a workable `hilbertSchmidtGate` for
the compact-support carrier `CompactLogTest`, removing the A0 single-point-window
obstruction?

Strategy: build an `ArchimedeanTraceSymbols` whose `Test = CompactLogTest`,
`hilbertSchmidtGate g` = "the windowed detector at g is self-adjoint AND
HS-trace-class".  Because `CompactLogTest` carries `HasCompactSupport` and the
detector factors are boundary-compact kernels, both conjuncts should be
provable from existing lemmas.  The wiring is one direction only
(`CompactLogTest.test : CompactLogTest → TestFunction`), no new estimate.

This probe only *type-checks the bridge*; it does not rewire the skeleton.
-/

import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform
open scoped InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair

/-- The compact-support carrier that the windowed HS-trace machinery owns. -/
abbrev HsTest := CCM25Concrete.CompactLogConvolution.CompactLogTest

/-- windowedBoundaryDetector is self-adjoint for every compact-support test. -/
theorem hsGate_selfAdjoint (g : HsTest) (a c : ℝ) :
    IsSelfAdjoint (windowedBoundaryDetector g a c) :=
  windowedBoundaryDetector_isSelfAdjoint g a c

/--
The enabling bridge: the HS-trace machinery is already trace-class over a full
Hilbert basis, so the detector is a genuine HS operator (not a bare `det`).
This is the conjunct that A0's single-point window could not provide.
-/
theorem hsGate_traceClass_enablingBridge
    (g : HsTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (signedBoundaryOperator g a c negativeBasis positiveBasis outputBasis
        globalBasis) :=
  signedBoundaryOperator_isTraceClassAlong
    g a c negativeBasis positiveBasis outputBasis globalBasis

end Dev
end Source
end ConnesWeilRH