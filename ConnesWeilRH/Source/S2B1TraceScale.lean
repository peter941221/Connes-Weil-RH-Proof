/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.ObjectTheoremBasePackage
import ConnesWeilRH.Source.CCM25Concrete.Package

/-!
# S2-B1 trace-scale source data

This module is the source-layer home for the fixed-tuple S2-B1 analytic
exclusion data.  It does not prove the analytic rows by itself.  Instead, it
keeps the six fixed-tuple source obligations inspectable before they are
assembled into the theorem-base package:

* support-square / `QW_lambda` read-off through a common source scalar;
* rank / zero-mode classification;
* no-strip rank / pole classification;
* endpoint-strip `Cdef` domination;
* no-extra-bulk exclusion;
* no-hidden finite-part-subtraction exclusion.
-/

namespace ConnesWeilRH
namespace Source

/--
Fixed-tuple S2-B1 theorem data.

The support-square leg is stored as source read-off data rather than only as
the final equality.  The remaining five legs are stored as constructor inputs,
so downstream rows can be derived without losing the source-proof shape.
-/
structure S2B1FixedTupleTheoremData
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  supportSquareQWLambdaReadOff :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      A W lambda archimedeanTest weilTest
  rankZeroMode :
    S2B1FixedTupleRankZeroModeConstructorInput
      A W lambda archimedeanTest weilTest
  noStripRankPole :
    S2B1FixedTupleNoStripRankPoleConstructorInput
      A W lambda archimedeanTest weilTest
  endpointStripCdef :
    S2B1FixedTupleEndpointStripCdefConstructorInput
      A W lambda archimedeanTest weilTest
  noExtraBulk :
    S2B1FixedTupleNoExtraBulkConstructorInput
      A W lambda archimedeanTest weilTest
  noHiddenFinitePartSubtraction :
    S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      A W lambda archimedeanTest weilTest

namespace S2B1FixedTupleTheoremData

def supportSquareRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data : S2B1FixedTupleTheoremData A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaRow
      A W lambda archimedeanTest weilTest :=
  data.supportSquareQWLambdaReadOff.toRow

def rankZeroModeRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data : S2B1FixedTupleTheoremData A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleRankZeroModeRow
      A W lambda archimedeanTest weilTest :=
  data.rankZeroMode.toRow

def noStripRankPoleRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data : S2B1FixedTupleTheoremData A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoStripRankPoleRow
      A W lambda archimedeanTest weilTest :=
  data.noStripRankPole.toRow

def endpointStripCdefRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data : S2B1FixedTupleTheoremData A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleEndpointStripCdefRow
      A W lambda archimedeanTest weilTest :=
  data.endpointStripCdef.toRow

def noExtraBulkRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data : S2B1FixedTupleTheoremData A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoExtraBulkRow
      A W lambda archimedeanTest weilTest :=
  data.noExtraBulk.toRow

def noHiddenFinitePartSubtractionRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data : S2B1FixedTupleTheoremData A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      A W lambda archimedeanTest weilTest :=
  data.noHiddenFinitePartSubtraction.toRow

def toPackage
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} (hlambda : 1 < lambda)
    {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data : S2B1FixedTupleTheoremData A W lambda archimedeanTest weilTest) :
    S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      A W lambda archimedeanTest weilTest where
  oneLtLambda := hlambda
  supportSquareQWLambdaRow := data.supportSquareRow
  rankZeroModeRow := data.rankZeroModeRow
  noStripRankPoleRow := data.noStripRankPoleRow
  endpointStripCdefRow := data.endpointStripCdefRow
  noExtraBulkRow := data.noExtraBulkRow
  noHiddenFinitePartSubtractionRow :=
    data.noHiddenFinitePartSubtractionRow

end S2B1FixedTupleTheoremData

/--
Same-cutoff S2-B1 theorem data for every legal fixed tuple.

This is the source-facing statement that should eventually be proved from the
analytic S2-B1 proof package.  The theorem-base constructor can consume it
without hiding the individual fixed-tuple rows.
-/
structure S2B1TraceScaleTheoremData
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols) where
  fixedTuple :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FixedTupleTheoremData A W lambda archimedeanTest weilTest

namespace S2B1TraceScaleTheoremData

def toConstructorInput
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (data : S2B1TraceScaleTheoremData A W) :
    S2B1TraceScaleAnalyticExclusionConstructorInput A W where
  supportSquareQWLambdaReadOffSourceData :=
    fun lambda hlambda archimedeanTest weilTest =>
      (data.fixedTuple lambda hlambda archimedeanTest weilTest).supportSquareQWLambdaReadOff
  rankZeroModeConstructorInput :=
    fun lambda hlambda archimedeanTest weilTest =>
      (data.fixedTuple lambda hlambda archimedeanTest weilTest).rankZeroMode
  noStripRankPoleConstructorInput :=
    fun lambda hlambda archimedeanTest weilTest =>
      (data.fixedTuple lambda hlambda archimedeanTest weilTest).noStripRankPole
  endpointStripCdefConstructorInput :=
    fun lambda hlambda archimedeanTest weilTest =>
      (data.fixedTuple lambda hlambda archimedeanTest weilTest).endpointStripCdef
  noExtraBulkConstructorInput :=
    fun lambda hlambda archimedeanTest weilTest =>
      (data.fixedTuple lambda hlambda archimedeanTest weilTest).noExtraBulk
  noHiddenFinitePartSubtractionConstructorInput :=
    fun lambda hlambda archimedeanTest weilTest =>
      (data.fixedTuple lambda hlambda archimedeanTest weilTest).noHiddenFinitePartSubtraction

def fixedTuplePackage
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (data : S2B1TraceScaleTheoremData A W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      A W lambda archimedeanTest weilTest :=
  (data.fixedTuple lambda hlambda archimedeanTest weilTest).toPackage hlambda

end S2B1TraceScaleTheoremData

/--
Concrete CC20 support-square read-off for the normalized square seed.

This is a genuine definitional proof: for the normalized square trace object,
the support-square trace is the square of the stored trace amplitude.  It
proves only the CC20 support-square leg of the S2-B1 read-off; the CCM25
identification with `QW_lambda` is a separate arithmetic/Weil-form theorem.
-/
theorem normalized_seed_cc20_support_square_trace_read_off
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (g : A.Test) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.supportSquareTrace g =
      A.traceAmplitude g ^ 2 :=
  CC20Concrete.TraceScale.normalized_seed_trace_object_support_square_eq_trace_amplitude_sq
    A remainders g

def normalizedSeedSupportSquareReadOffSourceScalar
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (g : A.Test) : ℝ :=
  A.traceAmplitude g ^ 2

def normalizedSeedSupportSquareCC20ReadOffData
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.supportSquareTrace g =
      normalizedSeedSupportSquareReadOffSourceScalar A g :=
  normalized_seed_cc20_support_square_trace_read_off A remainders g

theorem normalized_seed_cc20_source_no_defect_trace_read_off
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (g : A.Test) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.sourceNoDefectTrace g =
      A.traceAmplitude g ^ 2 :=
  CC20Concrete.TraceScale.normalized_seed_trace_object_source_no_defect_eq_trace_amplitude_sq
    A remainders g

theorem normalized_seed_cc20_positive_trace_read_off
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (g : A.Test) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.positiveTrace g =
      A.traceAmplitude g ^ 2 :=
  CC20Concrete.TraceScale.normalized_seed_trace_object_positive_trace_eq_trace_amplitude_sq
    A remainders g

theorem normalized_seed_cc20_support_square_eq_source_no_defect
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (g : A.Test) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.supportSquareTrace g =
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.sourceNoDefectTrace g := by
  rw [normalized_seed_cc20_support_square_trace_read_off,
    normalized_seed_cc20_source_no_defect_trace_read_off]

theorem normalized_seed_cc20_positive_trace_eq_support_square
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (g : A.Test) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.positiveTrace g =
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.supportSquareTrace g := by
  rw [normalized_seed_cc20_positive_trace_read_off,
    normalized_seed_cc20_support_square_trace_read_off]

theorem normalized_seed_cc20_hilbert_schmidt_gate_iff
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (g : A.Test) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.hilbertSchmidtGate g ↔
      A.traceClass g ∧ A.cyclicLegal g :=
  CC20Concrete.TraceScale.normalized_seed_trace_object_hilbert_schmidt_gate_iff
    A remainders g

theorem normalized_seed_cc20_positive_trace_nonnegative
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (g : A.Test) :
    0 ≤
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.positiveTrace g :=
  CC20Concrete.TraceScale.normalized_seed_trace_object_positive_trace_nonnegative
    A remainders g

theorem normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
    {W : WeilFormSymbols} {lambda : ℝ}
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda) :
    W.qwLambda lambda weilTest weilTest =
      W.archimedeanTerm (W.convolutionStar weilTest weilTest) +
        W.polePairing weilTest -
          CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
            ccm25 :=
  CCM25Concrete.Package.qw_lambda_formula_source_evaluator_common_atoms_of_package
    ccm25

noncomputable def normalizedSeedCCM25RestrictedEvaluatorScalar
    (W : WeilFormSymbols) {lambda : ℝ} (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda) : ℝ :=
  W.archimedeanTerm (W.convolutionStar weilTest weilTest) +
    W.polePairing weilTest -
      CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
        ccm25

noncomputable def normalizedSeedMatchedToCCM25Evaluator
    (base : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols) {lambda : ℝ} (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols where
  Test := base.Test
  traceAmplitude :=
    fun _g => Real.sqrt
      (normalizedSeedCCM25RestrictedEvaluatorScalar W weilTest ccm25)
  traceClass := base.traceClass
  cyclicLegal := base.cyclicLegal

theorem normalized_seed_matched_trace_amplitude_sq_eq_ccm25_evaluator
    (base : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols) {lambda : ℝ} (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda)
    (h_nonneg :
      0 ≤ normalizedSeedCCM25RestrictedEvaluatorScalar W weilTest ccm25)
    (g :
      (normalizedSeedMatchedToCCM25Evaluator
        base W weilTest ccm25).Test) :
    (normalizedSeedMatchedToCCM25Evaluator
      base W weilTest ccm25).traceAmplitude g ^ 2 =
      normalizedSeedCCM25RestrictedEvaluatorScalar W weilTest ccm25 := by
  dsimp [normalizedSeedMatchedToCCM25Evaluator]
  exact Real.sq_sqrt h_nonneg

def normalizedSeedSupportSquareQWLambdaReadOffFromCCM25Scalar
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (lambda : ℝ)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (ccm25ScalarReadOff :
      normalizedSeedSupportSquareReadOffSourceScalar A g =
        W.qwLambda lambda weilTest weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols
      W lambda g weilTest where
  sourceRestrictedTraceScalar :=
    normalizedSeedSupportSquareReadOffSourceScalar A g
  cc20SupportSquareTraceReadOff :=
    normalizedSeedSupportSquareCC20ReadOffData A remainders g
  ccm25QWLambdaSourceReadOff := ccm25ScalarReadOff

def normalizedSeedSupportSquareQWLambdaReadOffFromCCM25EvaluatorIdentity
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (lambda : ℝ)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda)
    (ccm25ScalarReadOff :
      normalizedSeedSupportSquareReadOffSourceScalar A g =
        W.archimedeanTerm (W.convolutionStar weilTest weilTest) +
          W.polePairing weilTest -
            CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
              ccm25) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols
      W lambda g weilTest :=
  normalizedSeedSupportSquareQWLambdaReadOffFromCCM25Scalar
    A W remainders lambda g weilTest
    (by
      rw [ccm25ScalarReadOff]
      rw [normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
        weilTest ccm25])

/--
Actual normalized-seed scalar identification for the support-square/`QW_lambda`
row.

This is the narrow source theorem still needed for the actual CC20 trace seed:
its support-square scalar `traceAmplitude ^ 2` must equal the CCM25 restricted
evaluator for the same fixed tuple.
-/
structure NormalizedSeedRestrictedEvaluatorScalarIdentification
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    {lambda : ℝ}
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda) where
  traceAmplitudeSquare_eq_restrictedEvaluator :
    normalizedSeedSupportSquareReadOffSourceScalar A g =
      normalizedSeedCCM25RestrictedEvaluatorScalar W weilTest ccm25

/--
Package-free actual normalized-seed scalar identification.

This is the exact theorem-base first-row target: the actual seed's
`traceAmplitude ^ 2` equals the CCM25 restricted `QW_lambda` value.  The
evaluator-level record above is a stronger way to prove it when a concrete
CCM25 arithmetic package is available.
-/
structure NormalizedSeedQWLambdaScalarIdentification
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (lambda : ℝ)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction) where
  traceAmplitudeSquare_eq_qwLambda :
    normalizedSeedSupportSquareReadOffSourceScalar A g =
      W.qwLambda lambda weilTest weilTest

def normalizedSeedQWLambdaScalarIdentificationOfRestrictedEvaluator
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    {lambda : ℝ}
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda)
    (identification :
      NormalizedSeedRestrictedEvaluatorScalarIdentification
        A W remainders g weilTest ccm25) :
    NormalizedSeedQWLambdaScalarIdentification
      A W remainders lambda g weilTest where
  traceAmplitudeSquare_eq_qwLambda := by
    rw [identification.traceAmplitudeSquare_eq_restrictedEvaluator]
    symm
    exact normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
      weilTest ccm25

def normalizedSeedSupportSquareQWLambdaReadOffOfQWLambdaScalarIdentification
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (lambda : ℝ)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (identification :
      NormalizedSeedQWLambdaScalarIdentification
        A W remainders lambda g weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols
      W lambda g weilTest :=
  normalizedSeedSupportSquareQWLambdaReadOffFromCCM25Scalar
    A W remainders lambda g weilTest
    identification.traceAmplitudeSquare_eq_qwLambda

def normalizedSeedSupportSquareQWLambdaReadOffOfScalarIdentification
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    {lambda : ℝ}
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda)
    (identification :
      NormalizedSeedRestrictedEvaluatorScalarIdentification
        A W remainders g weilTest ccm25) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols
      W lambda g weilTest :=
  normalizedSeedSupportSquareQWLambdaReadOffFromCCM25EvaluatorIdentity
    A W remainders lambda g weilTest ccm25
    identification.traceAmplitudeSquare_eq_restrictedEvaluator

theorem normalized_seed_support_square_eq_qwLambda_of_qwLambda_scalar_identification
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (lambda : ℝ)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (identification :
      NormalizedSeedQWLambdaScalarIdentification
        A W remainders lambda g weilTest) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.supportSquareTrace g =
      W.qwLambda lambda weilTest weilTest :=
  (normalizedSeedSupportSquareQWLambdaReadOffOfQWLambdaScalarIdentification
    A W remainders lambda g weilTest identification).toRow.supportSquareMainTermEqualsQWLambda

theorem normalized_seed_support_square_eq_qwLambda_of_scalar_identification
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    {lambda : ℝ}
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda)
    (identification :
      NormalizedSeedRestrictedEvaluatorScalarIdentification
        A W remainders g weilTest ccm25) :
    (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      A remainders).archimedeanSymbols.supportSquareTrace g =
      W.qwLambda lambda weilTest weilTest :=
  (normalizedSeedSupportSquareQWLambdaReadOffOfScalarIdentification
    A W remainders g weilTest ccm25 identification).toRow.supportSquareMainTermEqualsQWLambda

/--
Actual normalized-seed fixed-tuple theorem data from the scalar identification
and the remaining S2-B1 rows.

Unlike the matched-seed constructor below, this does not change the seed.  The
new input is exactly the actual-source scalar theorem that must be proved.
-/
def normalizedSeedFixedTupleTheoremDataOfScalarIdentificationAndRemainingRows
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    {lambda : ℝ}
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda)
    (identification :
      NormalizedSeedRestrictedEvaluatorScalarIdentification
        A W remainders g weilTest ccm25)
    (rankZeroMode :
      S2B1FixedTupleRankZeroModeConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest)
    (noStripRankPole :
      S2B1FixedTupleNoStripRankPoleConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest)
    (endpointStripCdef :
      S2B1FixedTupleEndpointStripCdefConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest)
    (noExtraBulk :
      S2B1FixedTupleNoExtraBulkConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest)
    (noHiddenFinitePartSubtraction :
      S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest) :
    S2B1FixedTupleTheoremData
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols
      W lambda g weilTest where
  supportSquareQWLambdaReadOff :=
    normalizedSeedSupportSquareQWLambdaReadOffOfScalarIdentification
      A W remainders g weilTest ccm25 identification
  rankZeroMode := rankZeroMode
  noStripRankPole := noStripRankPole
  endpointStripCdef := endpointStripCdef
  noExtraBulk := noExtraBulk
  noHiddenFinitePartSubtraction := noHiddenFinitePartSubtraction

/--
Actual normalized-seed fixed-tuple theorem data from the package-free
`traceAmplitude ^ 2 = QW_lambda` scalar identification.
-/
def normalizedSeedFixedTupleTheoremDataOfQWLambdaScalarIdentification
    (A : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    (remainders : CC20Concrete.TraceScale.CC20TracePackageRemainderData A)
    (lambda : ℝ)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols.Test)
    (weilTest : TestFunction)
    (identification :
      NormalizedSeedQWLambdaScalarIdentification
        A W remainders lambda g weilTest)
    (rankZeroMode :
      S2B1FixedTupleRankZeroModeConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest)
    (noStripRankPole :
      S2B1FixedTupleNoStripRankPoleConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest)
    (endpointStripCdef :
      S2B1FixedTupleEndpointStripCdefConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest)
    (noExtraBulk :
      S2B1FixedTupleNoExtraBulkConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest)
    (noHiddenFinitePartSubtraction :
      S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          A remainders).archimedeanSymbols
        W lambda g weilTest) :
    S2B1FixedTupleTheoremData
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        A remainders).archimedeanSymbols
      W lambda g weilTest where
  supportSquareQWLambdaReadOff :=
    normalizedSeedSupportSquareQWLambdaReadOffOfQWLambdaScalarIdentification
      A W remainders lambda g weilTest identification
  rankZeroMode := rankZeroMode
  noStripRankPole := noStripRankPole
  endpointStripCdef := endpointStripCdef
  noExtraBulk := noExtraBulk
  noHiddenFinitePartSubtraction := noHiddenFinitePartSubtraction

noncomputable def normalizedSeedMatchedSupportSquareQWLambdaReadOff
    (base : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    {lambda : ℝ}
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (normalizedSeedMatchedToCCM25Evaluator
          base W weilTest ccm25))
    (h_nonneg :
      0 ≤ normalizedSeedCCM25RestrictedEvaluatorScalar W weilTest ccm25)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        (normalizedSeedMatchedToCCM25Evaluator
          base W weilTest ccm25)
        remainders).archimedeanSymbols.Test) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        (normalizedSeedMatchedToCCM25Evaluator
          base W weilTest ccm25)
        remainders).archimedeanSymbols
      W lambda g weilTest :=
  normalizedSeedSupportSquareQWLambdaReadOffFromCCM25EvaluatorIdentity
    (normalizedSeedMatchedToCCM25Evaluator base W weilTest ccm25)
    W remainders lambda g weilTest ccm25
    (normalized_seed_matched_trace_amplitude_sq_eq_ccm25_evaluator
      base W weilTest ccm25 h_nonneg g)

/--
Matched-seed S2-B1 fixed-tuple data with only the support-square/`QW_lambda`
leg supplied by the concrete scalar proof.

The remaining five rows stay explicit inputs.  This prevents the matched-seed
construction from being mistaken for a full S2-B1 analytic exclusion proof.
-/
noncomputable def matchedSeedFixedTupleTheoremDataOfRemainingRows
    (base : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (W : WeilFormSymbols)
    {lambda : ℝ}
    (weilTest : TestFunction)
    (ccm25 :
      CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        W weilTest lambda)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (normalizedSeedMatchedToCCM25Evaluator
          base W weilTest ccm25))
    (h_nonneg :
      0 ≤ normalizedSeedCCM25RestrictedEvaluatorScalar W weilTest ccm25)
    (g :
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        (normalizedSeedMatchedToCCM25Evaluator
          base W weilTest ccm25)
        remainders).archimedeanSymbols.Test)
    (rankZeroMode :
      S2B1FixedTupleRankZeroModeConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          (normalizedSeedMatchedToCCM25Evaluator
            base W weilTest ccm25)
          remainders).archimedeanSymbols
        W lambda g weilTest)
    (noStripRankPole :
      S2B1FixedTupleNoStripRankPoleConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          (normalizedSeedMatchedToCCM25Evaluator
            base W weilTest ccm25)
          remainders).archimedeanSymbols
        W lambda g weilTest)
    (endpointStripCdef :
      S2B1FixedTupleEndpointStripCdefConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          (normalizedSeedMatchedToCCM25Evaluator
            base W weilTest ccm25)
          remainders).archimedeanSymbols
        W lambda g weilTest)
    (noExtraBulk :
      S2B1FixedTupleNoExtraBulkConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          (normalizedSeedMatchedToCCM25Evaluator
            base W weilTest ccm25)
          remainders).archimedeanSymbols
        W lambda g weilTest)
    (noHiddenFinitePartSubtraction :
      S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
          (normalizedSeedMatchedToCCM25Evaluator
            base W weilTest ccm25)
          remainders).archimedeanSymbols
        W lambda g weilTest) :
    S2B1FixedTupleTheoremData
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        (normalizedSeedMatchedToCCM25Evaluator
          base W weilTest ccm25)
        remainders).archimedeanSymbols
      W lambda g weilTest where
  supportSquareQWLambdaReadOff :=
    normalizedSeedMatchedSupportSquareQWLambdaReadOff
      base W weilTest ccm25 remainders h_nonneg g
  rankZeroMode := rankZeroMode
  noStripRankPole := noStripRankPole
  endpointStripCdef := endpointStripCdef
  noExtraBulk := noExtraBulk
  noHiddenFinitePartSubtraction := noHiddenFinitePartSubtraction

end Source
end ConnesWeilRH
