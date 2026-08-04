/-
A2 carrier probe (Seam B, step 2): can `SourceTestAlgebra` be brought onto the
`CompactLogTest` carrier so the concrete gate exists over a NONZERO support
test?  Records the structural boundary found.

Findings (type-level, no skeleton rewire):

1. `SourceTestAlgebra` (AnalyticCoreBase.lean:109) REQUIRES
   `legacy : LegacyTestEquiv Test`, i.e. `encode : Test → TestFunction`,
   `decode : TestFunction → Test`, and the round-trip laws
   (`decode_encode`/`encode_decode`, AnalyticCoreBase.lean:28-32).

2. A `LegacyTestEquiv CompactLogTest` cannot exist: `decode : TestFunction →
   CompactLogTest` would need every Schwartz `TestFunction` F to have
   `HasCompactSupport F`, which is false for general Schwartz tests.
   `CompactLogTest` (CCM25Concrete/CompactLogConvolution.lean:29-31) is the
   TYPE of *compactly supported* smooth tests; it is a strict subset of
   `TestFunction`, so no bijection Test ⇌ TestFunction exists.

3. Therefore a `CompactLogTest`-carrier `SourceTestAlgebra` is NOT trivially
   constructible.  A0 cannot be cleared by a localized carrier swap at the
   `SourceTestAlgebra`/`SourceTraceScaleData` boundary; the legacy bijection
   is structural.

4. The mathematically honest nonzero element exists (`G_v`, the Groskin
   finite-dictionary test, docs/proofs/041), but on a GROWING-support family;
   forcing it into one fixed window is precisely the A0 single-point-empty
   regime, and the odd/even (Herglotz) reduction makes the odd positive
   definiteness RH-equivalent (docs/proofs/041 §5).  So the A0 resolution is
   NOT a small carrier edit: it needs either (i) a `Test` type with a real
   compact-support equality shell, or (ii) replacing the support-containment
   gate with an operator/trace-class gate that the existing HS machinery
   (`ordinaryTrace_positiveComposition_re_nonnegative` + concrete Hilbert
   basis, `A1SeamBOperatorCarrierProbe`) already supplies.

Type-check that the two clean building blocks used by any resolution exist;
no fake helpers.
-/

import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace A2CarrierProbe

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open PositiveTrace

/-- The operator-side object (from the closed A1 bridge): the compact root
detector is an endomorphism of the crossing space, self-adjoint, and an HS
sandwich.  This is the gate component a "traceClass = self-adjoint ∧ HS
trace-class" concrete interpretation would need. -/
abbrev HsTest := CCM25Concrete.CompactLogConvolution.CompactLogTest

theorem a2_detector_exists
    (g : HsTest) (a c : ℝ) :
    IsSelfAdjoint (windowedBoundaryDetector g a c) :=
  windowedBoundaryDetector_isSelfAdjoint g a c

theorem a2_hs_witness_exists
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (data : BasisHilbertSchmidtData globalBasis) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (BasisHilbertSchmidtData.positiveComposition data)).re :=
  data.ordinaryTrace_positiveComposition_re_nonnegative

end A2CarrierProbe
end Dev
end Source
end ConnesWeilRH