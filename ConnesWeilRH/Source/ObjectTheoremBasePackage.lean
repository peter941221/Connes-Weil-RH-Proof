/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.TheoremBase
import ConnesWeilRH.Source.CC20Concrete.TraceScale
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData

/-!
# Source-object theorem-base staging package

Goal 2A collects the Goal 1B source models into a source-object staging layer.
This module does not build `SourceObjectPackage`, common-test data, route
front ends, `RouteCertificate`, or an unconditional RH theorem.
-/

namespace ConnesWeilRH
namespace Source

/--
CC20 trace-package remainder rows outside the S2-B1 no-bulk pair.

These fields are not supplied by the normalized trace-scale seed.  The S2-B1
no-bulk rows stay separate as `CC20CCMTraceScaleNoBulkWitness`, so callers can
keep the same-cutoff source theorem visible.
-/
structure S2B1NormalizedCC20RemainderRowsOutsideNoBulk
    (seed : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols) where
  sourceTraceTest :
    (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      seed).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        seed).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            seed).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop
  sourceNoDefectTraceReadOff : Prop
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop
  sourceRemainderObject : Prop
  sourceRemainderObjectHolds : sourceRemainderObject
  sourceRemainderAfterQ : Prop
  sourceRemainderAfterQHolds : sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport : Prop
  cc20PostQRemainderFixedSSoninTransportHolds :
    cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm : Prop
  sourceProjectionDefectNormalFormHolds :
    sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification : Prop
  sourceRankPoleLedgerIdentificationHolds :
    sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination : Prop
  sourceEndpointStripRemainderCdefDominationHolds :
    sourceEndpointStripRemainderCdefDomination
  noHiddenPositiveDefectOutsideCdef : Prop
  noHiddenPositiveDefectOutsideCdefHolds :
    noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport : Prop
  sourceBoundedComparisonTraceIdealTransportHolds :
    sourceBoundedComparisonTraceIdealTransport

/--
Source-owned scalar data for the finite-part normal form of one S2-B1 fixed
tuple.

This is the object-level anchor below `S2B1FinitePartScalarInterface`.  It
names the three source scalars before they are projected into the theorem-facing
interface.  It intentionally records scalars only; the equalities proving the
normal form remain separate rows.
-/
structure S2B1FinitePartSourceScalarData
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  sourceActualFinitePart : ℝ
  sourceNormalizedFinitePart : ℝ
  sourceSubtractedFinitePartTerm : ℝ

/--
Named scalar interface for the finite-part normal form of one S2-B1 fixed
tuple.

These fields deliberately do not identify the finite-part scalars with the
support-square trace, no-defect trace, or `QW_lambda`.  That bridge needs a
separate source theorem.  This interface only prevents the no-hidden
finite-part row from being proved against anonymous real numbers.
-/
structure S2B1FinitePartScalarInterface
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  actualFinitePartScalar : ℝ
  normalizedFinitePartScalar : ℝ
  subtractedFinitePartScalar : ℝ

namespace S2B1FinitePartScalarInterface

def finitePartNormalizationFixedStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (scalars :
      S2B1FinitePartScalarInterface
        A W lambda archimedeanTest weilTest) : Prop :=
  scalars.actualFinitePartScalar = scalars.normalizedFinitePartScalar

def noSubtractedFinitePartTermStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (scalars :
      S2B1FinitePartScalarInterface
        A W lambda archimedeanTest weilTest) : Prop :=
  scalars.subtractedFinitePartScalar = 0

end S2B1FinitePartScalarInterface

namespace S2B1FinitePartSourceScalarData

def toScalarInterface
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartSourceScalarData
        A W lambda archimedeanTest weilTest) :
    S2B1FinitePartScalarInterface
      A W lambda archimedeanTest weilTest where
  actualFinitePartScalar := data.sourceActualFinitePart
  normalizedFinitePartScalar := data.sourceNormalizedFinitePart
  subtractedFinitePartScalar := data.sourceSubtractedFinitePartTerm

end S2B1FinitePartSourceScalarData

/--
Scalar CC20 trace-package remainder rows outside the scalar seed.

The scalar seed fixes the scalar trace family and its nonnegativity, but it
does not choose the CC20 source trace test or discharge the source remainder
rows.  This record is the source-interface home for those scalar rows before
they are assembled into `CC20TracePackageRemainderData`.
-/
structure NormalizedScalarCC20RemainderRows
    (scalarSeed : CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols) where
  sourceTraceTest :
    (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        scalarSeed)).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              scalarSeed)).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop
  sourceNoDefectTraceReadOff : Prop
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop
  sourceRemainderObject : Prop
  sourceRemainderAfterQ : Prop
  cc20PostQRemainderFixedSSoninTransport : Prop
  sourceProjectionDefectNormalForm : Prop
  sourceRankPoleLedgerIdentification : Prop
  sourceEndpointStripRemainderCdefDomination : Prop
  noBulkScaleTermOutsideLedger : Prop
  noHiddenFinitePartSubtraction : Prop
  noBulkScaleTermOutsideLedgerHolds : noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtractionHolds : noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerAt :
    ℝ →
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)).archimedeanSymbols.Test →
        TestFunction → Prop
  noHiddenFinitePartSubtractionAt :
    ℝ →
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)).archimedeanSymbols.Test →
        TestFunction → Prop
  noBulkScaleTermOutsideLedgerAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            scalarSeed)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noBulkScaleTermOutsideLedgerAt lambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            scalarSeed)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noHiddenFinitePartSubtractionAt lambda archimedeanTest weilTest
  noHiddenPositiveDefectOutsideCdef : Prop
  sourceBoundedComparisonTraceIdealTransport : Prop

namespace NormalizedScalarCC20RemainderRows

def toRemainderData
    {scalarSeed : CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols}
    (rows : NormalizedScalarCC20RemainderRows scalarSeed) :
    CC20Concrete.TraceScale.CC20TracePackageRemainderData
      (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        scalarSeed) where
  sourceTraceTest := rows.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    rows.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity := rows.sourceOperatorIdentity
  sourceHilbertSchmidtGate := rows.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger := rows.sourcePerMoveCyclicityLedger
  sourceNoDefectTraceReadOff := rows.sourceNoDefectTraceReadOff
  sourceRemainderOrientationWInftyEqLMinusD :=
    rows.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    rows.sourceRemainderOrientationWInftyEqSMinusE
  sourceRemainderObject := rows.sourceRemainderObject
  sourceRemainderAfterQ := rows.sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport :=
    rows.cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm := rows.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    rows.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    rows.sourceEndpointStripRemainderCdefDomination
  noBulkScaleTermOutsideLedger := rows.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction := rows.noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerHolds :=
    rows.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    rows.noHiddenFinitePartSubtractionHolds
  noBulkScaleTermOutsideLedgerAt := rows.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt := rows.noHiddenFinitePartSubtractionAt
  noBulkScaleTermOutsideLedgerAtHolds :=
    rows.noBulkScaleTermOutsideLedgerAtHolds
  noHiddenFinitePartSubtractionAtHolds :=
    rows.noHiddenFinitePartSubtractionAtHolds
  noHiddenPositiveDefectOutsideCdef :=
    rows.noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport :=
    rows.sourceBoundedComparisonTraceIdealTransport

end NormalizedScalarCC20RemainderRows

/--
The two S2-B1 no-bulk rows at a fixed source-test cutoff.

The rows are kept separate so the divergent-bulk obstruction and the hidden
finite-part-subtraction obstruction can be audited independently before they
are packaged as a `CC20CCMTraceScaleNoBulkWitness`.
-/
structure S2B1TraceScaleNoBulkRows
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols) where
  noBulkScaleTermOutsideLedgerAt :
    ℝ → A.Test → TestFunction → Prop
  noHiddenFinitePartSubtractionAt :
    ℝ → A.Test → TestFunction → Prop
  noBulkScaleTermOutsideLedgerAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        noBulkScaleTermOutsideLedgerAt lambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        noHiddenFinitePartSubtractionAt lambda archimedeanTest weilTest

namespace S2B1TraceScaleNoBulkRows

def toWitness
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (rows : S2B1TraceScaleNoBulkRows A W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    CC20CCMTraceScaleNoBulkWitness
      A W lambda archimedeanTest weilTest where
  noBulkScaleTermOutsideLedger :=
    rows.noBulkScaleTermOutsideLedgerAt lambda archimedeanTest weilTest
  noHiddenFinitePartSubtraction :=
    rows.noHiddenFinitePartSubtractionAt lambda archimedeanTest weilTest
  noBulkScaleTermOutsideLedgerHolds :=
    rows.noBulkScaleTermOutsideLedgerAtHolds
      lambda hlambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionHolds :=
    rows.noHiddenFinitePartSubtractionAtHolds
      lambda hlambda archimedeanTest weilTest

end S2B1TraceScaleNoBulkRows

namespace S2B1NormalizedCC20RemainderRowsOutsideNoBulk

def toRemainderData
    {seed : CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols}
    {W : WeilFormSymbols}
    (rows : S2B1NormalizedCC20RemainderRowsOutsideNoBulk seed)
    (noBulkRows :
      S2B1TraceScaleNoBulkRows
        (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          seed).archimedeanSymbols W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        seed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    CC20Concrete.TraceScale.CC20TracePackageRemainderData seed where
  sourceTraceTest := rows.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    rows.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity := rows.sourceOperatorIdentity
  sourceHilbertSchmidtGate := rows.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger := rows.sourcePerMoveCyclicityLedger
  sourceNoDefectTraceReadOff := rows.sourceNoDefectTraceReadOff
  sourceRemainderOrientationWInftyEqLMinusD :=
    rows.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    rows.sourceRemainderOrientationWInftyEqSMinusE
  sourceRemainderObject := rows.sourceRemainderObject
  sourceRemainderAfterQ := rows.sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport :=
    rows.cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm :=
    rows.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    rows.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    rows.sourceEndpointStripRemainderCdefDomination
  noBulkScaleTermOutsideLedger :=
    (noBulkRows.toWitness lambda hlambda archimedeanTest
      weilTest).noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction :=
    (noBulkRows.toWitness lambda hlambda archimedeanTest
      weilTest).noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerHolds :=
    (noBulkRows.toWitness lambda hlambda archimedeanTest
      weilTest).noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    (noBulkRows.toWitness lambda hlambda archimedeanTest
      weilTest).noHiddenFinitePartSubtractionHolds
  noBulkScaleTermOutsideLedgerAt := noBulkRows.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt :=
    noBulkRows.noHiddenFinitePartSubtractionAt
  noBulkScaleTermOutsideLedgerAtHolds :=
    noBulkRows.noBulkScaleTermOutsideLedgerAtHolds
  noHiddenFinitePartSubtractionAtHolds :=
    noBulkRows.noHiddenFinitePartSubtractionAtHolds
  noHiddenPositiveDefectOutsideCdef :=
    rows.noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport :=
    rows.sourceBoundedComparisonTraceIdealTransport

end S2B1NormalizedCC20RemainderRowsOutsideNoBulk

/--
Term-ledger rows for the S2-B1 trace-scale no-bulk theorem.

This record mirrors the source-term ledger: every possible entry point for a
hidden trace-scale scalar is named before the two final no-bulk rows are
derived.  The rows remain source/theorem-base obligations; this structure only
prevents the obligations from being collapsed into one opaque proposition.
-/
structure S2B1TraceScaleTermLedgerRows
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols) where
  rankZeroModeChannelClassifiedAt :
    ℝ → A.Test → TestFunction → Prop
  noStripPostQRemainderRankPoleClassifiedAt :
    ℝ → A.Test → TestFunction → Prop
  endpointStripBulkClassifiedIntoCdefAt :
    ℝ → A.Test → TestFunction → Prop
  endpointStripBoundaryTermsClassifiedAt :
    ℝ → A.Test → TestFunction → Prop
  sourceSeriesTailClassifiedIntoCdefAt :
    ℝ → A.Test → TestFunction → Prop
  cdefExhaustionOwnsEndpointStripAt :
    ℝ → A.Test → TestFunction → Prop
  noExtraBulkScaleTermAt :
    ℝ → A.Test → TestFunction → Prop
  finitePartSourceScalarDataAt :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FinitePartSourceScalarData
          A W lambda archimedeanTest weilTest
  supportSquareMainTermEqualsQWLambdaAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        A.supportSquareTrace archimedeanTest =
          W.qwLambda lambda weilTest weilTest
  rankZeroModeChannelClassifiedAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        rankZeroModeChannelClassifiedAt lambda archimedeanTest weilTest
  noStripPostQRemainderRankPoleClassifiedAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        noStripPostQRemainderRankPoleClassifiedAt lambda archimedeanTest weilTest
  endpointStripBulkClassifiedIntoCdefAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        endpointStripBulkClassifiedIntoCdefAt lambda archimedeanTest weilTest
  endpointStripBoundaryTermsClassifiedAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        endpointStripBoundaryTermsClassifiedAt lambda archimedeanTest weilTest
  sourceSeriesTailClassifiedIntoCdefAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        sourceSeriesTailClassifiedIntoCdefAt lambda archimedeanTest weilTest
  cdefExhaustionOwnsEndpointStripAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        cdefExhaustionOwnsEndpointStripAt lambda archimedeanTest weilTest
  noExtraBulkScaleTermAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        noExtraBulkScaleTermAt lambda archimedeanTest weilTest
  finitePartNormalizationFixedAtHolds :
    ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        ((finitePartSourceScalarDataAt lambda hlambda archimedeanTest
          weilTest).toScalarInterface).finitePartNormalizationFixedStatement
  noSubtractedFinitePartTermAtHolds :
    ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        ((finitePartSourceScalarDataAt lambda hlambda archimedeanTest
          weilTest).toScalarInterface).noSubtractedFinitePartTermStatement

structure S2B1TraceScaleAnalyticExclusionPackage
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols) where
  supportSquareMainTermEqualsQWLambdaAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        A.supportSquareTrace archimedeanTest =
          W.qwLambda lambda weilTest weilTest
  rankZeroModeChannelClassifiedAt :
    ℝ → A.Test → TestFunction → Prop
  rankZeroModeChannelClassifiedAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        rankZeroModeChannelClassifiedAt lambda archimedeanTest weilTest
  noStripPostQRemainderRankPoleClassifiedAt :
    ℝ → A.Test → TestFunction → Prop
  noStripPostQRemainderRankPoleClassifiedAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        noStripPostQRemainderRankPoleClassifiedAt lambda archimedeanTest weilTest
  endpointStripBulkClassifiedIntoCdefAt :
    ℝ → A.Test → TestFunction → Prop
  endpointStripBulkClassifiedIntoCdefAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        endpointStripBulkClassifiedIntoCdefAt lambda archimedeanTest weilTest
  endpointStripBoundaryTermsClassifiedAt :
    ℝ → A.Test → TestFunction → Prop
  endpointStripBoundaryTermsClassifiedAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        endpointStripBoundaryTermsClassifiedAt lambda archimedeanTest weilTest
  sourceSeriesTailClassifiedIntoCdefAt :
    ℝ → A.Test → TestFunction → Prop
  sourceSeriesTailClassifiedIntoCdefAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        sourceSeriesTailClassifiedIntoCdefAt lambda archimedeanTest weilTest
  cdefExhaustionOwnsEndpointStripAt :
    ℝ → A.Test → TestFunction → Prop
  cdefExhaustionOwnsEndpointStripAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        cdefExhaustionOwnsEndpointStripAt lambda archimedeanTest weilTest
  noExtraBulkScaleTermExcludedAt :
    ℝ → A.Test → TestFunction → Prop
  noExtraBulkScaleTermExcludedAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        noExtraBulkScaleTermExcludedAt lambda archimedeanTest weilTest
  finitePartSourceScalarDataAt :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FinitePartSourceScalarData
          A W lambda archimedeanTest weilTest
  finitePartNormalizationFixedAtHolds :
    ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        ((finitePartSourceScalarDataAt lambda hlambda archimedeanTest
          weilTest).toScalarInterface).finitePartNormalizationFixedStatement
  noSubtractedFinitePartTermAtHolds :
    ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        ((finitePartSourceScalarDataAt lambda hlambda archimedeanTest
          weilTest).toScalarInterface).noSubtractedFinitePartTermStatement

/-- Fixed-tuple support-square read-off row:
the CC20 support-square trace is the CCM25 restricted `QW_lambda` value for the
same tuple. -/
structure S2B1FixedTupleSupportSquareQWLambdaRow
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  supportSquareMainTermEqualsQWLambda :
    A.supportSquareTrace archimedeanTest =
      W.qwLambda lambda weilTest weilTest

/--
Constructor-facing support-square/QW_lambda row.

This exposes the exact equality that must be proved for the fixed tuple before
it is packaged as `S2B1FixedTupleSupportSquareQWLambdaRow`.
-/
structure S2B1FixedTupleSupportSquareQWLambdaConstructorInput
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  supportSquareMainTermEqualsQWLambdaAtHolds :
    A.supportSquareTrace archimedeanTest =
      W.qwLambda lambda weilTest weilTest

namespace S2B1FixedTupleSupportSquareQWLambdaConstructorInput

def toRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleSupportSquareQWLambdaConstructorInput
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaRow
      A W lambda archimedeanTest weilTest where
  supportSquareMainTermEqualsQWLambda :=
    data.supportSquareMainTermEqualsQWLambdaAtHolds

end S2B1FixedTupleSupportSquareQWLambdaConstructorInput

/--
Source read-off constructor for the fixed-tuple support-square/`QW_lambda`
row.

The final equality is not stored directly here.  Instead, CC20 and CCM25 must
both read off the same source restricted trace scalar.  The fixed-tuple row is
then obtained by transitivity, which keeps the two source obligations visible.
-/
structure S2B1FixedTupleSupportSquareQWLambdaReadOffConstructorInput
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  sourceRestrictedTraceScalar : ℝ
  cc20SupportSquareTraceReadOff :
    A.supportSquareTrace archimedeanTest =
      sourceRestrictedTraceScalar
  ccm25QWLambdaSourceReadOff :
    sourceRestrictedTraceScalar =
      W.qwLambda lambda weilTest weilTest

/--
Source data for the fixed-tuple support-square/`QW_lambda` read-off.

This is the formal source-layer home for the common scalar and the two source
read-off legs.  Constructor inputs are derived from this data instead of
storing a final equality directly.
-/
structure S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  sourceRestrictedTraceScalar : ℝ
  cc20SupportSquareTraceReadOff :
    A.supportSquareTrace archimedeanTest =
      sourceRestrictedTraceScalar
  ccm25QWLambdaSourceReadOff :
    sourceRestrictedTraceScalar =
      W.qwLambda lambda weilTest weilTest

namespace S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData

def transportArchimedean
    {A B : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {weilTest : TestFunction}
    (h : A = B) (archimedeanTest : B.Test)
    (data :
      S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
        A W lambda (cast (congrArg ArchimedeanTraceSymbols.Test h.symm)
          archimedeanTest) weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      B W lambda archimedeanTest weilTest := by
  subst h
  exact data

def toConstructorInput
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffConstructorInput
      A W lambda archimedeanTest weilTest where
  sourceRestrictedTraceScalar := data.sourceRestrictedTraceScalar
  cc20SupportSquareTraceReadOff := data.cc20SupportSquareTraceReadOff
  ccm25QWLambdaSourceReadOff := data.ccm25QWLambdaSourceReadOff

def toRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaRow
      A W lambda archimedeanTest weilTest where
  supportSquareMainTermEqualsQWLambda :=
    data.cc20SupportSquareTraceReadOff.trans
      data.ccm25QWLambdaSourceReadOff

end S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData

namespace S2B1FixedTupleSupportSquareQWLambdaReadOffConstructorInput

def toConstructorInput
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleSupportSquareQWLambdaReadOffConstructorInput
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaConstructorInput
      A W lambda archimedeanTest weilTest where
  supportSquareMainTermEqualsQWLambdaAtHolds :=
    data.cc20SupportSquareTraceReadOff.trans
      data.ccm25QWLambdaSourceReadOff

def toRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleSupportSquareQWLambdaReadOffConstructorInput
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleSupportSquareQWLambdaRow
      A W lambda archimedeanTest weilTest :=
  data.toConstructorInput.toRow

end S2B1FixedTupleSupportSquareQWLambdaReadOffConstructorInput

/-- Fixed-tuple rank/zero-mode row. -/
structure S2B1FixedTupleRankZeroModeRow
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  rankZeroModeChannelClassified : Prop
  rankZeroModeChannelClassifiedHolds :
    rankZeroModeChannelClassified

/-- Constructor-facing rank/zero-mode source rows for one fixed tuple. -/
structure S2B1FixedTupleRankZeroModeConstructorInput
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  rankLedgerChannelIdentified : Prop
  zeroModeChannelEliminated : Prop
  rankLedgerChannelIdentifiedHolds :
    rankLedgerChannelIdentified
  zeroModeChannelEliminatedHolds :
    zeroModeChannelEliminated

namespace S2B1FixedTupleRankZeroModeConstructorInput

def transportArchimedean
    {A B : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {weilTest : TestFunction}
    (h : A = B) (archimedeanTest : B.Test)
    (data :
      S2B1FixedTupleRankZeroModeConstructorInput
        A W lambda (cast (congrArg ArchimedeanTraceSymbols.Test h.symm)
          archimedeanTest) weilTest) :
    S2B1FixedTupleRankZeroModeConstructorInput
      B W lambda archimedeanTest weilTest := by
  subst h
  exact data

def toRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleRankZeroModeConstructorInput
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleRankZeroModeRow
      A W lambda archimedeanTest weilTest where
  rankZeroModeChannelClassified :=
    data.rankLedgerChannelIdentified ∧ data.zeroModeChannelEliminated
  rankZeroModeChannelClassifiedHolds :=
    ⟨data.rankLedgerChannelIdentifiedHolds,
      data.zeroModeChannelEliminatedHolds⟩

end S2B1FixedTupleRankZeroModeConstructorInput

/-- Fixed-tuple no-strip rank/pole row. -/
structure S2B1FixedTupleNoStripRankPoleRow
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  noStripPostQRemainderRankPoleClassified : Prop
  noStripPostQRemainderRankPoleClassifiedHolds :
    noStripPostQRemainderRankPoleClassified

/-- Constructor-facing no-strip rank/pole source rows for one fixed tuple. -/
structure S2B1FixedTupleNoStripRankPoleConstructorInput
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  noStripRemainderChannelsExhausted : Prop
  noStripRankLedgerIdentified : Prop
  noStripPoleLedgerIdentified : Prop
  noStripRemainderChannelsExhaustedHolds :
    noStripRemainderChannelsExhausted
  noStripRankLedgerIdentifiedHolds :
    noStripRankLedgerIdentified
  noStripPoleLedgerIdentifiedHolds :
    noStripPoleLedgerIdentified

namespace S2B1FixedTupleNoStripRankPoleConstructorInput

def transportArchimedean
    {A B : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {weilTest : TestFunction}
    (h : A = B) (archimedeanTest : B.Test)
    (data :
      S2B1FixedTupleNoStripRankPoleConstructorInput
        A W lambda (cast (congrArg ArchimedeanTraceSymbols.Test h.symm)
          archimedeanTest) weilTest) :
    S2B1FixedTupleNoStripRankPoleConstructorInput
      B W lambda archimedeanTest weilTest := by
  subst h
  exact data

def toRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleNoStripRankPoleConstructorInput
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoStripRankPoleRow
      A W lambda archimedeanTest weilTest where
  noStripPostQRemainderRankPoleClassified :=
    data.noStripRemainderChannelsExhausted ∧
      data.noStripRankLedgerIdentified ∧
        data.noStripPoleLedgerIdentified
  noStripPostQRemainderRankPoleClassifiedHolds :=
    ⟨data.noStripRemainderChannelsExhaustedHolds,
      data.noStripRankLedgerIdentifiedHolds,
      data.noStripPoleLedgerIdentifiedHolds⟩

end S2B1FixedTupleNoStripRankPoleConstructorInput

/-- Fixed-tuple endpoint-strip `Cdef` ownership row. -/
structure S2B1FixedTupleEndpointStripCdefRow
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  endpointStripBulkClassifiedIntoCdef : Prop
  endpointStripBulkClassifiedIntoCdefHolds :
    endpointStripBulkClassifiedIntoCdef
  endpointStripBoundaryTermsClassified : Prop
  endpointStripBoundaryTermsClassifiedHolds :
    endpointStripBoundaryTermsClassified
  sourceSeriesTailClassifiedIntoCdef : Prop
  sourceSeriesTailClassifiedIntoCdefHolds :
    sourceSeriesTailClassifiedIntoCdef
  cdefExhaustionOwnsEndpointStrip : Prop
  cdefExhaustionOwnsEndpointStripHolds :
    cdefExhaustionOwnsEndpointStrip

/-- Constructor-facing endpoint-strip `Cdef` source rows for one fixed tuple. -/
structure S2B1FixedTupleEndpointStripCdefConstructorInput
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  endpointStripBulkNormalForm : Prop
  endpointStripBulkCdefDomination : Prop
  endpointStripBoundaryTransport : Prop
  endpointStripBoundaryCdefDomination : Prop
  sourceSeriesTailTransport : Prop
  sourceSeriesTailCdefDomination : Prop
  cdefNormFormula : Prop
  fixedTestCdefExhaustion : Prop
  endpointStripBulkNormalFormHolds :
    endpointStripBulkNormalForm
  endpointStripBulkCdefDominationHolds :
    endpointStripBulkCdefDomination
  endpointStripBoundaryTransportHolds :
    endpointStripBoundaryTransport
  endpointStripBoundaryCdefDominationHolds :
    endpointStripBoundaryCdefDomination
  sourceSeriesTailTransportHolds :
    sourceSeriesTailTransport
  sourceSeriesTailCdefDominationHolds :
    sourceSeriesTailCdefDomination
  cdefNormFormulaHolds :
    cdefNormFormula
  fixedTestCdefExhaustionHolds :
    fixedTestCdefExhaustion

namespace S2B1FixedTupleEndpointStripCdefConstructorInput

def transportArchimedean
    {A B : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {weilTest : TestFunction}
    (h : A = B) (archimedeanTest : B.Test)
    (data :
      S2B1FixedTupleEndpointStripCdefConstructorInput
        A W lambda (cast (congrArg ArchimedeanTraceSymbols.Test h.symm)
          archimedeanTest) weilTest) :
    S2B1FixedTupleEndpointStripCdefConstructorInput
      B W lambda archimedeanTest weilTest := by
  subst h
  exact data

def toRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleEndpointStripCdefConstructorInput
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleEndpointStripCdefRow
      A W lambda archimedeanTest weilTest where
  endpointStripBulkClassifiedIntoCdef :=
    data.endpointStripBulkNormalForm ∧ data.endpointStripBulkCdefDomination
  endpointStripBulkClassifiedIntoCdefHolds :=
    ⟨data.endpointStripBulkNormalFormHolds,
      data.endpointStripBulkCdefDominationHolds⟩
  endpointStripBoundaryTermsClassified :=
    data.endpointStripBoundaryTransport ∧ data.endpointStripBoundaryCdefDomination
  endpointStripBoundaryTermsClassifiedHolds :=
    ⟨data.endpointStripBoundaryTransportHolds,
      data.endpointStripBoundaryCdefDominationHolds⟩
  sourceSeriesTailClassifiedIntoCdef :=
    data.sourceSeriesTailTransport ∧ data.sourceSeriesTailCdefDomination
  sourceSeriesTailClassifiedIntoCdefHolds :=
    ⟨data.sourceSeriesTailTransportHolds,
      data.sourceSeriesTailCdefDominationHolds⟩
  cdefExhaustionOwnsEndpointStrip :=
    data.cdefNormFormula ∧ data.fixedTestCdefExhaustion
  cdefExhaustionOwnsEndpointStripHolds :=
    ⟨data.cdefNormFormulaHolds,
      data.fixedTestCdefExhaustionHolds⟩

end S2B1FixedTupleEndpointStripCdefConstructorInput

/-- Fixed-tuple no-extra-bulk row. -/
structure S2B1FixedTupleNoExtraBulkRow
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  noExtraBulkScaleTermExcluded : Prop
  noExtraBulkScaleTermExcludedHolds :
    noExtraBulkScaleTermExcluded

/-- Constructor-facing no-extra-bulk source rows for one fixed tuple. -/
structure S2B1FixedTupleNoExtraBulkConstructorInput
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  positiveTraceScaleDecomposition : Prop
  ledgerTermsExhaustTraceScaleBulk : Prop
  noBulkScaleTermOutsideLedger : Prop
  positiveTraceScaleDecompositionHolds :
    positiveTraceScaleDecomposition
  ledgerTermsExhaustTraceScaleBulkHolds :
    ledgerTermsExhaustTraceScaleBulk
  noBulkScaleTermOutsideLedgerHolds :
    noBulkScaleTermOutsideLedger

namespace S2B1FixedTupleNoExtraBulkConstructorInput

def transportArchimedean
    {A B : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {weilTest : TestFunction}
    (h : A = B) (archimedeanTest : B.Test)
    (data :
      S2B1FixedTupleNoExtraBulkConstructorInput
        A W lambda (cast (congrArg ArchimedeanTraceSymbols.Test h.symm)
          archimedeanTest) weilTest) :
    S2B1FixedTupleNoExtraBulkConstructorInput
      B W lambda archimedeanTest weilTest := by
  subst h
  exact data

def toRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleNoExtraBulkConstructorInput
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoExtraBulkRow
      A W lambda archimedeanTest weilTest where
  noExtraBulkScaleTermExcluded :=
    data.positiveTraceScaleDecomposition ∧
      data.ledgerTermsExhaustTraceScaleBulk ∧
        data.noBulkScaleTermOutsideLedger
  noExtraBulkScaleTermExcludedHolds :=
    ⟨data.positiveTraceScaleDecompositionHolds,
      data.ledgerTermsExhaustTraceScaleBulkHolds,
      data.noBulkScaleTermOutsideLedgerHolds⟩

end S2B1FixedTupleNoExtraBulkConstructorInput

/-- Fixed-tuple no-hidden-finite-part-subtraction row. -/
structure S2B1FixedTupleNoHiddenFinitePartSubtractionRow
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  noHiddenFinitePartSubtractionExcluded : Prop
  noHiddenFinitePartSubtractionExcludedHolds :
    noHiddenFinitePartSubtractionExcluded

/-- Constructor-facing no-hidden finite-part subtraction rows for one tuple. -/
structure S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
    (_A : ArchimedeanTraceSymbols) (_W : WeilFormSymbols)
    (_lambda : ℝ) (_archimedeanTest : _A.Test) (_weilTest : TestFunction) where
  finitePartNormalizationFixed : Prop
  noSubtractedFinitePartTerm : Prop
  finitePartNormalizationFixedHolds :
    finitePartNormalizationFixed
  noSubtractedFinitePartTermHolds :
    noSubtractedFinitePartTerm

namespace S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput

def transportArchimedean
    {A B : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {weilTest : TestFunction}
    (h : A = B) (archimedeanTest : B.Test)
    (data :
      S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
        A W lambda (cast (congrArg ArchimedeanTraceSymbols.Test h.symm)
          archimedeanTest) weilTest) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      B W lambda archimedeanTest weilTest := by
  subst h
  exact data

def toRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      A W lambda archimedeanTest weilTest where
  noHiddenFinitePartSubtractionExcluded :=
    data.finitePartNormalizationFixed ∧ data.noSubtractedFinitePartTerm
  noHiddenFinitePartSubtractionExcludedHolds :=
    ⟨data.finitePartNormalizationFixedHolds,
      data.noSubtractedFinitePartTermHolds⟩

end S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput

/--
Finite-part scalar normal form for one S2-B1 fixed tuple.

The route needs this layer before the no-hidden finite-part row can become a
real theorem target.  The scalar interface names the quantities that a source
proof or later concrete Lean model must identify:

* the finite part actually read from the trace side;
* the normalized finite part allowed by the source convention;
* the extra finite-part term that would have been subtracted if a hidden
  correction survived.
-/
structure S2B1FinitePartNormalFormData
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  scalars :
    S2B1FinitePartScalarInterface
      A W lambda archimedeanTest weilTest

namespace S2B1FinitePartNormalFormData

def actualFinitePart
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartNormalFormData
        A W lambda archimedeanTest weilTest) : ℝ :=
  data.scalars.actualFinitePartScalar

def normalizedFinitePart
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartNormalFormData
        A W lambda archimedeanTest weilTest) : ℝ :=
  data.scalars.normalizedFinitePartScalar

def subtractedFinitePartTerm
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartNormalFormData
        A W lambda archimedeanTest weilTest) : ℝ :=
  data.scalars.subtractedFinitePartScalar

def finitePartNormalizationFixedStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartNormalFormData
        A W lambda archimedeanTest weilTest) : Prop :=
  data.scalars.finitePartNormalizationFixedStatement

def noSubtractedFinitePartTermStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartNormalFormData
        A W lambda archimedeanTest weilTest) : Prop :=
  data.scalars.noSubtractedFinitePartTermStatement

end S2B1FinitePartNormalFormData

/--
Proof rows for the finite-part normal form.

This is the first theorem-grade target below the no-hidden finite-part
constructor input.  It names both equalities against concrete scalar slots, so
future proof work can unfold definitions instead of proving an arbitrary
`Prop`.
-/
structure S2B1FinitePartNormalFormRows
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  data :
    S2B1FinitePartNormalFormData
      A W lambda archimedeanTest weilTest
  finitePartNormalizationFixedHolds :
    data.finitePartNormalizationFixedStatement
  noSubtractedFinitePartTermHolds :
    data.noSubtractedFinitePartTermStatement

/--
Source normal-form certificate for the finite-part leg.

This is the source-facing object that owns the two finite-part mathematical
equalities for one fixed tuple.  It keeps the scalar data and the proofs
together, so downstream code cannot combine scalars from one source object with
normal-form proofs from another.
-/
structure S2B1FinitePartSourceNormalFormData
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  sourceScalars :
    S2B1FinitePartSourceScalarData
      A W lambda archimedeanTest weilTest
  finitePartNormalizationFixedHolds :
    sourceScalars.toScalarInterface.finitePartNormalizationFixedStatement
  noSubtractedFinitePartTermHolds :
    sourceScalars.toScalarInterface.noSubtractedFinitePartTermStatement

structure S2B1FinitePartNormalizationFixedSourceRow
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  sourceActualFinitePart : ℝ
  sourceSubtractedFinitePartTerm : ℝ

namespace S2B1FinitePartNormalizationFixedSourceRow

def sourceScalars
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (row :
      S2B1FinitePartNormalizationFixedSourceRow
        A W lambda archimedeanTest weilTest) :
    S2B1FinitePartSourceScalarData
      A W lambda archimedeanTest weilTest where
  sourceActualFinitePart := row.sourceActualFinitePart
  sourceNormalizedFinitePart := row.sourceActualFinitePart
  sourceSubtractedFinitePartTerm := row.sourceSubtractedFinitePartTerm

def statement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (row :
      S2B1FinitePartNormalizationFixedSourceRow
        A W lambda archimedeanTest weilTest) : Prop :=
  row.sourceScalars.toScalarInterface.finitePartNormalizationFixedStatement

theorem statement_holds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (row :
      S2B1FinitePartNormalizationFixedSourceRow
        A W lambda archimedeanTest weilTest) :
    row.statement :=
  rfl

end S2B1FinitePartNormalizationFixedSourceRow

structure S2B1FinitePartNoSubtractedTermSourceRow
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  sourceActualFinitePart : ℝ

namespace S2B1FinitePartNoSubtractedTermSourceRow

def sourceScalars
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (row :
      S2B1FinitePartNoSubtractedTermSourceRow
        A W lambda archimedeanTest weilTest) :
    S2B1FinitePartSourceScalarData
      A W lambda archimedeanTest weilTest where
  sourceActualFinitePart := row.sourceActualFinitePart
  sourceNormalizedFinitePart := row.sourceActualFinitePart
  sourceSubtractedFinitePartTerm := 0

def normalizationStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (row :
      S2B1FinitePartNoSubtractedTermSourceRow
        A W lambda archimedeanTest weilTest) : Prop :=
  row.sourceScalars.toScalarInterface.finitePartNormalizationFixedStatement

theorem normalization_holds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (row :
      S2B1FinitePartNoSubtractedTermSourceRow
        A W lambda archimedeanTest weilTest) :
    row.normalizationStatement :=
  rfl

def statement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (row :
      S2B1FinitePartNoSubtractedTermSourceRow
        A W lambda archimedeanTest weilTest) : Prop :=
  row.sourceScalars.toScalarInterface.noSubtractedFinitePartTermStatement

theorem statement_holds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (row :
      S2B1FinitePartNoSubtractedTermSourceRow
        A W lambda archimedeanTest weilTest) :
    row.statement :=
  rfl

end S2B1FinitePartNoSubtractedTermSourceRow

namespace S2B1FinitePartSourceNormalFormData

def toNormalizationFixedSourceRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartSourceNormalFormData
        A W lambda archimedeanTest weilTest) :
    S2B1FinitePartNormalizationFixedSourceRow
      A W lambda archimedeanTest weilTest where
  sourceActualFinitePart :=
    data.sourceScalars.sourceActualFinitePart
  sourceSubtractedFinitePartTerm :=
    data.sourceScalars.sourceSubtractedFinitePartTerm

def toNoSubtractedTermSourceRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartSourceNormalFormData
        A W lambda archimedeanTest weilTest) :
    S2B1FinitePartNoSubtractedTermSourceRow
      A W lambda archimedeanTest weilTest where
  sourceActualFinitePart :=
    data.sourceScalars.sourceActualFinitePart

def toRows
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartSourceNormalFormData
        A W lambda archimedeanTest weilTest) :
    S2B1FinitePartNormalFormRows
      A W lambda archimedeanTest weilTest where
  data := { scalars := data.sourceScalars.toScalarInterface }
  finitePartNormalizationFixedHolds :=
    data.finitePartNormalizationFixedHolds
  noSubtractedFinitePartTermHolds :=
    data.noSubtractedFinitePartTermHolds

def toNoHiddenFinitePartConstructorInput
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartSourceNormalFormData
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      A W lambda archimedeanTest weilTest where
  finitePartNormalizationFixed :=
    data.sourceScalars.toScalarInterface.finitePartNormalizationFixedStatement
  noSubtractedFinitePartTerm :=
    data.sourceScalars.toScalarInterface.noSubtractedFinitePartTermStatement
  finitePartNormalizationFixedHolds :=
    data.finitePartNormalizationFixedHolds
  noSubtractedFinitePartTermHolds :=
    data.noSubtractedFinitePartTermHolds

def toNoHiddenFinitePartRow
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (data :
      S2B1FinitePartSourceNormalFormData
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      A W lambda archimedeanTest weilTest :=
  data.toNoHiddenFinitePartConstructorInput.toRow

end S2B1FinitePartSourceNormalFormData

/-- Source-facing theorem rows for the no-hidden finite-part subtraction leg. -/
structure S2B1NoHiddenFinitePartSubtractionConstructorRows
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  finitePartNormalizationFixed : Prop
  noSubtractedFinitePartTerm : Prop
  finitePartNormalizationFixedHolds :
    finitePartNormalizationFixed
  noSubtractedFinitePartTermHolds :
    noSubtractedFinitePartTerm

namespace S2B1NoHiddenFinitePartSubtractionConstructorRows

def toConstructorInput
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (rows :
      S2B1NoHiddenFinitePartSubtractionConstructorRows
        A W lambda archimedeanTest weilTest) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      A W lambda archimedeanTest weilTest where
  finitePartNormalizationFixed := rows.finitePartNormalizationFixed
  noSubtractedFinitePartTerm := rows.noSubtractedFinitePartTerm
  finitePartNormalizationFixedHolds :=
    rows.finitePartNormalizationFixedHolds
  noSubtractedFinitePartTermHolds :=
    rows.noSubtractedFinitePartTermHolds

end S2B1NoHiddenFinitePartSubtractionConstructorRows

namespace S2B1FinitePartNormalFormRows

def ofSourceScalarData
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (sourceScalars :
      S2B1FinitePartSourceScalarData
        A W lambda archimedeanTest weilTest)
    (finitePartNormalizationFixedHolds :
      sourceScalars.toScalarInterface.finitePartNormalizationFixedStatement)
    (noSubtractedFinitePartTermHolds :
      sourceScalars.toScalarInterface.noSubtractedFinitePartTermStatement) :
    S2B1FinitePartNormalFormRows
      A W lambda archimedeanTest weilTest where
  data := { scalars := sourceScalars.toScalarInterface }
  finitePartNormalizationFixedHolds := finitePartNormalizationFixedHolds
  noSubtractedFinitePartTermHolds := noSubtractedFinitePartTermHolds

def toNoHiddenFinitePartRows
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (rows :
      S2B1FinitePartNormalFormRows
        A W lambda archimedeanTest weilTest) :
    S2B1NoHiddenFinitePartSubtractionConstructorRows
      A W lambda archimedeanTest weilTest where
  finitePartNormalizationFixed :=
    rows.data.finitePartNormalizationFixedStatement
  noSubtractedFinitePartTerm :=
    rows.data.noSubtractedFinitePartTermStatement
  finitePartNormalizationFixedHolds :=
    rows.finitePartNormalizationFixedHolds
  noSubtractedFinitePartTermHolds :=
    rows.noSubtractedFinitePartTermHolds

end S2B1FinitePartNormalFormRows

/--
Fixed-tuple S2-B1 trace-scale exclusion data.

The source proof packages state S2-B1 for one route tuple
`(S, I, lambda, g, F_g, J)`.  This record mirrors that shape on the Lean side:
it binds the cutoff, archimedean trace test, and CCM25 Weil test before storing
the six target rows as named records.  The older
`S2B1TraceScaleAnalyticExclusionPackage` remains as a compatibility layer for
code that still wants all-cutoff/all-test rows.
-/
structure S2B1TraceScaleFixedTupleAnalyticExclusionPackage
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  oneLtLambda : 1 < lambda
  supportSquareQWLambdaRow :
    S2B1FixedTupleSupportSquareQWLambdaRow
      A W lambda archimedeanTest weilTest
  rankZeroModeRow :
    S2B1FixedTupleRankZeroModeRow
      A W lambda archimedeanTest weilTest
  noStripRankPoleRow :
    S2B1FixedTupleNoStripRankPoleRow
      A W lambda archimedeanTest weilTest
  endpointStripCdefRow :
    S2B1FixedTupleEndpointStripCdefRow
      A W lambda archimedeanTest weilTest
  noExtraBulkRow :
    S2B1FixedTupleNoExtraBulkRow
      A W lambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionRow :
    S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      A W lambda archimedeanTest weilTest

namespace S2B1TraceScaleAnalyticExclusionPackage

def toTermLedgerRows
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (pkg : S2B1TraceScaleAnalyticExclusionPackage A W) :
    S2B1TraceScaleTermLedgerRows A W where
  rankZeroModeChannelClassifiedAt :=
    pkg.rankZeroModeChannelClassifiedAt
  noStripPostQRemainderRankPoleClassifiedAt :=
    pkg.noStripPostQRemainderRankPoleClassifiedAt
  endpointStripBulkClassifiedIntoCdefAt :=
    pkg.endpointStripBulkClassifiedIntoCdefAt
  endpointStripBoundaryTermsClassifiedAt :=
    pkg.endpointStripBoundaryTermsClassifiedAt
  sourceSeriesTailClassifiedIntoCdefAt :=
    pkg.sourceSeriesTailClassifiedIntoCdefAt
  cdefExhaustionOwnsEndpointStripAt :=
    pkg.cdefExhaustionOwnsEndpointStripAt
  noExtraBulkScaleTermAt :=
    pkg.noExtraBulkScaleTermExcludedAt
  finitePartSourceScalarDataAt :=
    pkg.finitePartSourceScalarDataAt
  supportSquareMainTermEqualsQWLambdaAtHolds :=
    pkg.supportSquareMainTermEqualsQWLambdaAtHolds
  rankZeroModeChannelClassifiedAtHolds :=
    pkg.rankZeroModeChannelClassifiedAtHolds
  noStripPostQRemainderRankPoleClassifiedAtHolds :=
    pkg.noStripPostQRemainderRankPoleClassifiedAtHolds
  endpointStripBulkClassifiedIntoCdefAtHolds :=
    pkg.endpointStripBulkClassifiedIntoCdefAtHolds
  endpointStripBoundaryTermsClassifiedAtHolds :=
    pkg.endpointStripBoundaryTermsClassifiedAtHolds
  sourceSeriesTailClassifiedIntoCdefAtHolds :=
    pkg.sourceSeriesTailClassifiedIntoCdefAtHolds
  cdefExhaustionOwnsEndpointStripAtHolds :=
    pkg.cdefExhaustionOwnsEndpointStripAtHolds
  noExtraBulkScaleTermAtHolds :=
    pkg.noExtraBulkScaleTermExcludedAtHolds
  finitePartNormalizationFixedAtHolds :=
    pkg.finitePartNormalizationFixedAtHolds
  noSubtractedFinitePartTermAtHolds :=
    pkg.noSubtractedFinitePartTermAtHolds

end S2B1TraceScaleAnalyticExclusionPackage

namespace S2B1TraceScaleTermLedgerRows

def ordinaryPositiveTraceCarriedAt
    {A : ArchimedeanTraceSymbols} (_lambda : ℝ)
    (archimedeanTest : A.Test) (_weilTest : TestFunction) : Prop :=
  A.traceClass archimedeanTest →
    A.cyclicLegal archimedeanTest →
      A.positiveTrace archimedeanTest =
        A.supportSquareTrace archimedeanTest

def supportSquareSameFiniteLambdaScalarAt
    {A : ArchimedeanTraceSymbols} (_lambda : ℝ)
    (archimedeanTest : A.Test) (_weilTest : TestFunction) : Prop :=
  A.traceClass archimedeanTest →
    A.cyclicLegal archimedeanTest →
      A.supportSquareTrace archimedeanTest =
        A.sourceNoDefectTrace archimedeanTest

def supportSquareMainTermEqualsQWLambdaAt
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols} (lambda : ℝ)
    (archimedeanTest : A.Test) (weilTest : TestFunction) : Prop :=
  A.supportSquareTrace archimedeanTest = W.qwLambda lambda weilTest weilTest

def sourceNoDefectMainTermEqualsQWLambdaAt
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols} (lambda : ℝ)
    (archimedeanTest : A.Test) (weilTest : TestFunction) : Prop :=
  A.sourceNoDefectTrace archimedeanTest = W.qwLambda lambda weilTest weilTest

def restrictedCCM25CutoffMatchesTraceAt
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols} (lambda : ℝ)
    (_archimedeanTest : A.Test) (weilTest : TestFunction) : Prop :=
  W.qwLambda lambda weilTest weilTest =
    W.archimedeanTerm (W.convolutionStar weilTest weilTest) +
      W.polePairing weilTest -
        ∑ n ∈ W.restrictedPrimeIndexSet lambda,
          W.vonMangoldtWeight n * W.primePowerPairing n weilTest weilTest

def poleSeparatedNoDoubleCountingAt
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols} (_lambda : ℝ)
    (_archimedeanTest : A.Test) (weilTest : TestFunction) : Prop :=
  W.polePairing weilTest =
    W.poleFunctional (W.convolutionStar weilTest weilTest)

theorem ordinaryPositiveTraceCarriedAtHolds
    {A : ArchimedeanTraceSymbols}
    (ordinary :
      ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A) :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        ordinaryPositiveTraceCarriedAt lambda archimedeanTest weilTest := by
  intro _lambda _hlambda archimedeanTest _weilTest htrace hcyclic
  exact ordinary archimedeanTest htrace hcyclic

theorem supportSquareSameFiniteLambdaScalarAtHolds
    {A : ArchimedeanTraceSymbols}
    (traceSquare :
      ArchimedeanTraceSymbols.TraceSquareStatement A) :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        supportSquareSameFiniteLambdaScalarAt
          lambda archimedeanTest weilTest := by
  intro _lambda _hlambda archimedeanTest _weilTest htrace hcyclic
  exact (traceSquare archimedeanTest htrace hcyclic).1

theorem sourceNoDefectMainTermEqualsQWLambdaAt_of_supportSquare
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (supportSquareNoDefect :
      supportSquareSameFiniteLambdaScalarAt lambda archimedeanTest weilTest)
    (supportSquareQWLambda :
      supportSquareMainTermEqualsQWLambdaAt (W := W)
        lambda archimedeanTest weilTest)
    (htrace : A.traceClass archimedeanTest)
    (hcyclic : A.cyclicLegal archimedeanTest) :
    sourceNoDefectMainTermEqualsQWLambdaAt (W := W)
      lambda archimedeanTest weilTest := by
  exact (supportSquareNoDefect htrace hcyclic).symm.trans supportSquareQWLambda

theorem restrictedCCM25CutoffMatchesTraceAtHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W) :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        restrictedCCM25CutoffMatchesTraceAt
          (W := W) lambda archimedeanTest weilTest := by
  intro lambda hlambda _archimedeanTest weilTest
  exact qwLambdaFormula lambda hlambda weilTest

theorem poleSeparatedNoDoubleCountingAtHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (poleNormalization : WeilFormSymbols.PoleNormalizationStatement W) :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        poleSeparatedNoDoubleCountingAt
          (W := W) lambda archimedeanTest weilTest := by
  intro _lambda _hlambda _archimedeanTest weilTest
  exact poleNormalization weilTest

def noBulkScaleTermOutsideLedgerAt
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (rows : S2B1TraceScaleTermLedgerRows A W)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) : Prop :=
  ordinaryPositiveTraceCarriedAt lambda archimedeanTest weilTest ∧
    supportSquareSameFiniteLambdaScalarAt lambda archimedeanTest weilTest ∧
    supportSquareMainTermEqualsQWLambdaAt (W := W) lambda archimedeanTest weilTest ∧
    restrictedCCM25CutoffMatchesTraceAt
      (W := W) lambda archimedeanTest weilTest ∧
    rows.rankZeroModeChannelClassifiedAt lambda archimedeanTest weilTest ∧
    poleSeparatedNoDoubleCountingAt (W := W) lambda archimedeanTest weilTest ∧
    rows.noStripPostQRemainderRankPoleClassifiedAt lambda archimedeanTest weilTest ∧
    rows.endpointStripBulkClassifiedIntoCdefAt lambda archimedeanTest weilTest ∧
    rows.endpointStripBoundaryTermsClassifiedAt lambda archimedeanTest weilTest ∧
    rows.sourceSeriesTailClassifiedIntoCdefAt lambda archimedeanTest weilTest ∧
    rows.cdefExhaustionOwnsEndpointStripAt lambda archimedeanTest weilTest ∧
    rows.noExtraBulkScaleTermAt lambda archimedeanTest weilTest

def finitePartNormalFormRowsAt
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (rows : S2B1TraceScaleTermLedgerRows A W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    S2B1FinitePartNormalFormRows A W lambda archimedeanTest weilTest :=
  S2B1FinitePartNormalFormRows.ofSourceScalarData
    (rows.finitePartSourceScalarDataAt lambda hlambda archimedeanTest weilTest)
    (rows.finitePartNormalizationFixedAtHolds
      lambda hlambda archimedeanTest weilTest)
    (rows.noSubtractedFinitePartTermAtHolds
      lambda hlambda archimedeanTest weilTest)

def noHiddenFinitePartConstructorRowsAt
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (rows : S2B1TraceScaleTermLedgerRows A W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    S2B1NoHiddenFinitePartSubtractionConstructorRows
      A W lambda archimedeanTest weilTest :=
  (rows.finitePartNormalFormRowsAt
    lambda hlambda archimedeanTest weilTest).toNoHiddenFinitePartRows

def noHiddenFinitePartSubtractionStatementAt
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (rows : S2B1TraceScaleTermLedgerRows A W)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) : Prop :=
  supportSquareSameFiniteLambdaScalarAt lambda archimedeanTest weilTest ∧
    supportSquareMainTermEqualsQWLambdaAt (W := W) lambda archimedeanTest weilTest ∧
    restrictedCCM25CutoffMatchesTraceAt
      (W := W) lambda archimedeanTest weilTest ∧
    poleSeparatedNoDoubleCountingAt (W := W) lambda archimedeanTest weilTest ∧
    ∃ hlambda : 1 < lambda,
      (rows.noHiddenFinitePartConstructorRowsAt
        lambda hlambda archimedeanTest weilTest).finitePartNormalizationFixed ∧
      (rows.noHiddenFinitePartConstructorRowsAt
        lambda hlambda archimedeanTest weilTest).noSubtractedFinitePartTerm

def toNoBulkRows
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (rows : S2B1TraceScaleTermLedgerRows A W)
    (ordinary :
      ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A)
    (traceSquare :
      ArchimedeanTraceSymbols.TraceSquareStatement A)
    (qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W)
    (poleNormalization : WeilFormSymbols.PoleNormalizationStatement W) :
    S2B1TraceScaleNoBulkRows A W where
  noBulkScaleTermOutsideLedgerAt :=
    rows.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt :=
    rows.noHiddenFinitePartSubtractionStatementAt
  noBulkScaleTermOutsideLedgerAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    exact
      ⟨ordinaryPositiveTraceCarriedAtHolds ordinary
          lambda hlambda archimedeanTest weilTest,
        supportSquareSameFiniteLambdaScalarAtHolds traceSquare
          lambda hlambda archimedeanTest weilTest,
        rows.supportSquareMainTermEqualsQWLambdaAtHolds
          lambda hlambda archimedeanTest weilTest,
        restrictedCCM25CutoffMatchesTraceAtHolds qwLambdaFormula
          lambda hlambda archimedeanTest weilTest,
        rows.rankZeroModeChannelClassifiedAtHolds
          lambda hlambda archimedeanTest weilTest,
        poleSeparatedNoDoubleCountingAtHolds poleNormalization
          lambda hlambda archimedeanTest weilTest,
        rows.noStripPostQRemainderRankPoleClassifiedAtHolds
          lambda hlambda archimedeanTest weilTest,
        rows.endpointStripBulkClassifiedIntoCdefAtHolds
          lambda hlambda archimedeanTest weilTest,
        rows.endpointStripBoundaryTermsClassifiedAtHolds
          lambda hlambda archimedeanTest weilTest,
        rows.sourceSeriesTailClassifiedIntoCdefAtHolds
          lambda hlambda archimedeanTest weilTest,
        rows.cdefExhaustionOwnsEndpointStripAtHolds
          lambda hlambda archimedeanTest weilTest,
        rows.noExtraBulkScaleTermAtHolds
          lambda hlambda archimedeanTest weilTest⟩
  noHiddenFinitePartSubtractionAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    exact
      ⟨supportSquareSameFiniteLambdaScalarAtHolds traceSquare
          lambda hlambda archimedeanTest weilTest,
        rows.supportSquareMainTermEqualsQWLambdaAtHolds
          lambda hlambda archimedeanTest weilTest,
        restrictedCCM25CutoffMatchesTraceAtHolds qwLambdaFormula
          lambda hlambda archimedeanTest weilTest,
        poleSeparatedNoDoubleCountingAtHolds poleNormalization
          lambda hlambda archimedeanTest weilTest,
        ⟨hlambda,
          (rows.noHiddenFinitePartConstructorRowsAt
            lambda hlambda archimedeanTest weilTest).finitePartNormalizationFixedHolds,
          (rows.noHiddenFinitePartConstructorRowsAt
            lambda hlambda archimedeanTest weilTest).noSubtractedFinitePartTermHolds⟩⟩

end S2B1TraceScaleTermLedgerRows

namespace S2B1TraceScaleFixedTupleAnalyticExclusionPackage

def supportSquareMainTermEqualsQWLambda
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    A.supportSquareTrace archimedeanTest =
      W.qwLambda lambda weilTest weilTest :=
  pkg.supportSquareQWLambdaRow.supportSquareMainTermEqualsQWLambda

def rankZeroModeChannelClassified
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  pkg.rankZeroModeRow.rankZeroModeChannelClassified

def rankZeroModeChannelClassifiedHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    pkg.rankZeroModeChannelClassified :=
  pkg.rankZeroModeRow.rankZeroModeChannelClassifiedHolds

def noStripPostQRemainderRankPoleClassified
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  pkg.noStripRankPoleRow.noStripPostQRemainderRankPoleClassified

def noStripPostQRemainderRankPoleClassifiedHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    pkg.noStripPostQRemainderRankPoleClassified :=
  pkg.noStripRankPoleRow.noStripPostQRemainderRankPoleClassifiedHolds

def endpointStripBulkClassifiedIntoCdef
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  pkg.endpointStripCdefRow.endpointStripBulkClassifiedIntoCdef

def endpointStripBulkClassifiedIntoCdefHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    pkg.endpointStripBulkClassifiedIntoCdef :=
  pkg.endpointStripCdefRow.endpointStripBulkClassifiedIntoCdefHolds

def endpointStripBoundaryTermsClassified
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  pkg.endpointStripCdefRow.endpointStripBoundaryTermsClassified

def endpointStripBoundaryTermsClassifiedHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    pkg.endpointStripBoundaryTermsClassified :=
  pkg.endpointStripCdefRow.endpointStripBoundaryTermsClassifiedHolds

def sourceSeriesTailClassifiedIntoCdef
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  pkg.endpointStripCdefRow.sourceSeriesTailClassifiedIntoCdef

def sourceSeriesTailClassifiedIntoCdefHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    pkg.sourceSeriesTailClassifiedIntoCdef :=
  pkg.endpointStripCdefRow.sourceSeriesTailClassifiedIntoCdefHolds

def cdefExhaustionOwnsEndpointStrip
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  pkg.endpointStripCdefRow.cdefExhaustionOwnsEndpointStrip

def cdefExhaustionOwnsEndpointStripHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    pkg.cdefExhaustionOwnsEndpointStrip :=
  pkg.endpointStripCdefRow.cdefExhaustionOwnsEndpointStripHolds

def noExtraBulkScaleTermExcluded
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  pkg.noExtraBulkRow.noExtraBulkScaleTermExcluded

def noExtraBulkScaleTermExcludedHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    pkg.noExtraBulkScaleTermExcluded :=
  pkg.noExtraBulkRow.noExtraBulkScaleTermExcludedHolds

def noHiddenFinitePartSubtractionExcluded
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  pkg.noHiddenFinitePartSubtractionRow.noHiddenFinitePartSubtractionExcluded

def noHiddenFinitePartSubtractionExcludedHolds
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) :
    pkg.noHiddenFinitePartSubtractionExcluded :=
  pkg.noHiddenFinitePartSubtractionRow.noHiddenFinitePartSubtractionExcludedHolds

def noBulkScaleTermOutsideLedgerStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  S2B1TraceScaleTermLedgerRows.ordinaryPositiveTraceCarriedAt
      lambda archimedeanTest weilTest ∧
    S2B1TraceScaleTermLedgerRows.supportSquareSameFiniteLambdaScalarAt
      lambda archimedeanTest weilTest ∧
    S2B1TraceScaleTermLedgerRows.supportSquareMainTermEqualsQWLambdaAt
      (W := W) lambda archimedeanTest weilTest ∧
    S2B1TraceScaleTermLedgerRows.restrictedCCM25CutoffMatchesTraceAt
      (W := W) lambda archimedeanTest weilTest ∧
    pkg.rankZeroModeChannelClassified ∧
    S2B1TraceScaleTermLedgerRows.poleSeparatedNoDoubleCountingAt
      (W := W) lambda archimedeanTest weilTest ∧
    pkg.noStripPostQRemainderRankPoleClassified ∧
    pkg.endpointStripBulkClassifiedIntoCdef ∧
    pkg.endpointStripBoundaryTermsClassified ∧
    pkg.sourceSeriesTailClassifiedIntoCdef ∧
    pkg.cdefExhaustionOwnsEndpointStrip ∧
    pkg.noExtraBulkScaleTermExcluded

def noHiddenFinitePartSubtractionStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest) : Prop :=
  S2B1TraceScaleTermLedgerRows.supportSquareSameFiniteLambdaScalarAt
      lambda archimedeanTest weilTest ∧
    S2B1TraceScaleTermLedgerRows.supportSquareMainTermEqualsQWLambdaAt
      (W := W) lambda archimedeanTest weilTest ∧
    S2B1TraceScaleTermLedgerRows.restrictedCCM25CutoffMatchesTraceAt
      (W := W) lambda archimedeanTest weilTest ∧
    S2B1TraceScaleTermLedgerRows.poleSeparatedNoDoubleCountingAt
      (W := W) lambda archimedeanTest weilTest ∧
    pkg.noHiddenFinitePartSubtractionExcluded

def toWitness
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    {lambda : ℝ} {archimedeanTest : A.Test} {weilTest : TestFunction}
    (pkg :
      S2B1TraceScaleFixedTupleAnalyticExclusionPackage
        A W lambda archimedeanTest weilTest)
    (ordinary :
      ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A)
    (traceSquare :
      ArchimedeanTraceSymbols.TraceSquareStatement A)
    (qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W)
    (poleNormalization : WeilFormSymbols.PoleNormalizationStatement W) :
    CC20CCMTraceScaleNoBulkWitness A W lambda archimedeanTest weilTest where
  noBulkScaleTermOutsideLedger :=
    pkg.noBulkScaleTermOutsideLedgerStatement
  noHiddenFinitePartSubtraction :=
    pkg.noHiddenFinitePartSubtractionStatement
  noBulkScaleTermOutsideLedgerHolds := by
    exact
      ⟨S2B1TraceScaleTermLedgerRows.ordinaryPositiveTraceCarriedAtHolds
          ordinary lambda pkg.oneLtLambda archimedeanTest weilTest,
        S2B1TraceScaleTermLedgerRows.supportSquareSameFiniteLambdaScalarAtHolds
          traceSquare lambda pkg.oneLtLambda archimedeanTest weilTest,
        pkg.supportSquareMainTermEqualsQWLambda,
        S2B1TraceScaleTermLedgerRows.restrictedCCM25CutoffMatchesTraceAtHolds
          qwLambdaFormula lambda pkg.oneLtLambda archimedeanTest weilTest,
        pkg.rankZeroModeChannelClassifiedHolds,
        S2B1TraceScaleTermLedgerRows.poleSeparatedNoDoubleCountingAtHolds
          poleNormalization lambda pkg.oneLtLambda archimedeanTest weilTest,
        pkg.noStripPostQRemainderRankPoleClassifiedHolds,
        pkg.endpointStripBulkClassifiedIntoCdefHolds,
        pkg.endpointStripBoundaryTermsClassifiedHolds,
        pkg.sourceSeriesTailClassifiedIntoCdefHolds,
        pkg.cdefExhaustionOwnsEndpointStripHolds,
        pkg.noExtraBulkScaleTermExcludedHolds⟩
  noHiddenFinitePartSubtractionHolds := by
    exact
      ⟨S2B1TraceScaleTermLedgerRows.supportSquareSameFiniteLambdaScalarAtHolds
          traceSquare lambda pkg.oneLtLambda archimedeanTest weilTest,
        pkg.supportSquareMainTermEqualsQWLambda,
        S2B1TraceScaleTermLedgerRows.restrictedCCM25CutoffMatchesTraceAtHolds
          qwLambdaFormula lambda pkg.oneLtLambda archimedeanTest weilTest,
        S2B1TraceScaleTermLedgerRows.poleSeparatedNoDoubleCountingAtHolds
          poleNormalization lambda pkg.oneLtLambda archimedeanTest weilTest,
        pkg.noHiddenFinitePartSubtractionExcludedHolds⟩

def finitePartNormalFormRowsOfGlobalPackage
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (pkg : S2B1TraceScaleAnalyticExclusionPackage A W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    S2B1FinitePartNormalFormRows A W lambda archimedeanTest weilTest :=
  S2B1FinitePartNormalFormRows.ofSourceScalarData
    (pkg.finitePartSourceScalarDataAt lambda hlambda archimedeanTest weilTest)
    (pkg.finitePartNormalizationFixedAtHolds
      lambda hlambda archimedeanTest weilTest)
    (pkg.noSubtractedFinitePartTermAtHolds
      lambda hlambda archimedeanTest weilTest)

def noHiddenFinitePartSubtractionRowOfGlobalPackage
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (pkg : S2B1TraceScaleAnalyticExclusionPackage A W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      A W lambda archimedeanTest weilTest :=
  (finitePartNormalFormRowsOfGlobalPackage
    pkg lambda hlambda archimedeanTest weilTest).toNoHiddenFinitePartRows
      |>.toConstructorInput
      |>.toRow

def ofGlobalPackage
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (pkg : S2B1TraceScaleAnalyticExclusionPackage A W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      A W lambda archimedeanTest weilTest where
  oneLtLambda := hlambda
  supportSquareQWLambdaRow :=
    { supportSquareMainTermEqualsQWLambda :=
        pkg.supportSquareMainTermEqualsQWLambdaAtHolds
          lambda hlambda archimedeanTest weilTest }
  rankZeroModeRow :=
    { rankZeroModeChannelClassified :=
        pkg.rankZeroModeChannelClassifiedAt lambda archimedeanTest weilTest
      rankZeroModeChannelClassifiedHolds :=
        pkg.rankZeroModeChannelClassifiedAtHolds
          lambda hlambda archimedeanTest weilTest }
  noStripRankPoleRow :=
    { noStripPostQRemainderRankPoleClassified :=
        pkg.noStripPostQRemainderRankPoleClassifiedAt
          lambda archimedeanTest weilTest
      noStripPostQRemainderRankPoleClassifiedHolds :=
        pkg.noStripPostQRemainderRankPoleClassifiedAtHolds
          lambda hlambda archimedeanTest weilTest }
  endpointStripCdefRow :=
    { endpointStripBulkClassifiedIntoCdef :=
        pkg.endpointStripBulkClassifiedIntoCdefAt lambda archimedeanTest weilTest
      endpointStripBulkClassifiedIntoCdefHolds :=
        pkg.endpointStripBulkClassifiedIntoCdefAtHolds
          lambda hlambda archimedeanTest weilTest
      endpointStripBoundaryTermsClassified :=
        pkg.endpointStripBoundaryTermsClassifiedAt lambda archimedeanTest weilTest
      endpointStripBoundaryTermsClassifiedHolds :=
        pkg.endpointStripBoundaryTermsClassifiedAtHolds
          lambda hlambda archimedeanTest weilTest
      sourceSeriesTailClassifiedIntoCdef :=
        pkg.sourceSeriesTailClassifiedIntoCdefAt lambda archimedeanTest weilTest
      sourceSeriesTailClassifiedIntoCdefHolds :=
        pkg.sourceSeriesTailClassifiedIntoCdefAtHolds
          lambda hlambda archimedeanTest weilTest
      cdefExhaustionOwnsEndpointStrip :=
        pkg.cdefExhaustionOwnsEndpointStripAt lambda archimedeanTest weilTest
      cdefExhaustionOwnsEndpointStripHolds :=
        pkg.cdefExhaustionOwnsEndpointStripAtHolds
          lambda hlambda archimedeanTest weilTest }
  noExtraBulkRow :=
    { noExtraBulkScaleTermExcluded :=
        pkg.noExtraBulkScaleTermExcludedAt lambda archimedeanTest weilTest
      noExtraBulkScaleTermExcludedHolds :=
        pkg.noExtraBulkScaleTermExcludedAtHolds
          lambda hlambda archimedeanTest weilTest }
  noHiddenFinitePartSubtractionRow :=
    noHiddenFinitePartSubtractionRowOfGlobalPackage
      pkg lambda hlambda archimedeanTest weilTest

end S2B1TraceScaleFixedTupleAnalyticExclusionPackage

/--
Constructor-facing S2-B1 analytic exclusion input.

The real S2-B1 review surface is the fixed tuple package: support-square
read-off, rank/zero-mode, no-strip rank/pole, endpoint-strip `Cdef`,
no-extra-bulk, and no-hidden finite-part subtraction.  The global
`S2B1TraceScaleAnalyticExclusionPackage` is reconstructed from these
fixed-tuple rows.
-/
structure S2B1TraceScaleAnalyticExclusionConstructorInput
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols) where
  supportSquareQWLambdaReadOffSourceData :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
          A W lambda archimedeanTest weilTest
  rankZeroModeConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FixedTupleRankZeroModeConstructorInput
          A W lambda archimedeanTest weilTest
  noStripRankPoleConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FixedTupleNoStripRankPoleConstructorInput
          A W lambda archimedeanTest weilTest
  endpointStripCdefConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FixedTupleEndpointStripCdefConstructorInput
          A W lambda archimedeanTest weilTest
  noExtraBulkConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FixedTupleNoExtraBulkConstructorInput
          A W lambda archimedeanTest weilTest
  finitePartSourceNormalFormData :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest : A.Test,
      ∀ weilTest : TestFunction,
        S2B1FinitePartSourceNormalFormData
          A W lambda archimedeanTest weilTest

namespace S2B1TraceScaleAnalyticExclusionConstructorInput

def fixedTuple
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (data : S2B1TraceScaleAnalyticExclusionConstructorInput A W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      A W lambda archimedeanTest weilTest where
  oneLtLambda := hlambda
  supportSquareQWLambdaRow :=
    (data.supportSquareQWLambdaReadOffSourceData
      lambda hlambda archimedeanTest weilTest).toRow
  rankZeroModeRow :=
    (data.rankZeroModeConstructorInput
      lambda hlambda archimedeanTest weilTest).toRow
  noStripRankPoleRow :=
    (data.noStripRankPoleConstructorInput
      lambda hlambda archimedeanTest weilTest).toRow
  endpointStripCdefRow :=
    (data.endpointStripCdefConstructorInput
      lambda hlambda archimedeanTest weilTest).toRow
  noExtraBulkRow :=
    (data.noExtraBulkConstructorInput
      lambda hlambda archimedeanTest weilTest).toRow
  noHiddenFinitePartSubtractionRow :=
    let normalForm :=
      data.finitePartSourceNormalFormData
        lambda hlambda archimedeanTest weilTest
    normalForm.toNoHiddenFinitePartRow

def toTermLedgerRows
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (data : S2B1TraceScaleAnalyticExclusionConstructorInput A W) :
    S2B1TraceScaleTermLedgerRows A W where
  rankZeroModeChannelClassifiedAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.rankZeroModeChannelClassified
  noStripPostQRemainderRankPoleClassifiedAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.noStripPostQRemainderRankPoleClassified
  endpointStripBulkClassifiedIntoCdefAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.endpointStripBulkClassifiedIntoCdef
  endpointStripBoundaryTermsClassifiedAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.endpointStripBoundaryTermsClassified
  sourceSeriesTailClassifiedIntoCdefAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.sourceSeriesTailClassifiedIntoCdef
  cdefExhaustionOwnsEndpointStripAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.cdefExhaustionOwnsEndpointStrip
  noExtraBulkScaleTermAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.noExtraBulkScaleTermExcluded
  finitePartSourceScalarDataAt :=
    fun lambda hlambda archimedeanTest weilTest =>
      (data.finitePartSourceNormalFormData
        lambda hlambda archimedeanTest weilTest).sourceScalars
  supportSquareMainTermEqualsQWLambdaAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact row.supportSquareMainTermEqualsQWLambda
  rankZeroModeChannelClassifiedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact ⟨hlambda, row.rankZeroModeChannelClassifiedHolds⟩
  noStripPostQRemainderRankPoleClassifiedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact ⟨hlambda, row.noStripPostQRemainderRankPoleClassifiedHolds⟩
  endpointStripBulkClassifiedIntoCdefAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact ⟨hlambda, row.endpointStripBulkClassifiedIntoCdefHolds⟩
  endpointStripBoundaryTermsClassifiedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact ⟨hlambda, row.endpointStripBoundaryTermsClassifiedHolds⟩
  sourceSeriesTailClassifiedIntoCdefAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact ⟨hlambda, row.sourceSeriesTailClassifiedIntoCdefHolds⟩
  cdefExhaustionOwnsEndpointStripAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact ⟨hlambda, row.cdefExhaustionOwnsEndpointStripHolds⟩
  noExtraBulkScaleTermAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact ⟨hlambda, row.noExtraBulkScaleTermExcludedHolds⟩
  finitePartNormalizationFixedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    exact
      (data.finitePartSourceNormalFormData
        lambda hlambda archimedeanTest weilTest).finitePartNormalizationFixedHolds
  noSubtractedFinitePartTermAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    exact
      (data.finitePartSourceNormalFormData
        lambda hlambda archimedeanTest weilTest).noSubtractedFinitePartTermHolds

def noBulkWitness
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (data : S2B1TraceScaleAnalyticExclusionConstructorInput A W)
    (ordinary :
      ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A)
    (traceSquare :
      ArchimedeanTraceSymbols.TraceSquareStatement A)
    (qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W)
    (poleNormalization : WeilFormSymbols.PoleNormalizationStatement W)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : A.Test) (weilTest : TestFunction) :
    CC20CCMTraceScaleNoBulkWitness A W lambda archimedeanTest weilTest :=
  (data.fixedTuple lambda hlambda archimedeanTest weilTest).toWitness
    ordinary traceSquare qwLambdaFormula poleNormalization

def toNoBulkRows
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (data : S2B1TraceScaleAnalyticExclusionConstructorInput A W)
    (ordinary :
      ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A)
    (traceSquare :
      ArchimedeanTraceSymbols.TraceSquareStatement A)
    (qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W)
    (poleNormalization : WeilFormSymbols.PoleNormalizationStatement W) :
    S2B1TraceScaleNoBulkRows A W :=
  data.toTermLedgerRows.toNoBulkRows
    ordinary traceSquare qwLambdaFormula poleNormalization

theorem noBulkStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (data : S2B1TraceScaleAnalyticExclusionConstructorInput A W)
    (ordinary :
      ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A)
    (traceSquare :
      ArchimedeanTraceSymbols.TraceSquareStatement A)
    (qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W)
    (poleNormalization : WeilFormSymbols.PoleNormalizationStatement W) :
    CC20CCMTraceScaleNoBulkStatement A W := by
  intro lambda hlambda archimedeanTest weilTest
  exact
    ⟨(data.toNoBulkRows ordinary traceSquare qwLambdaFormula
      poleNormalization).toWitness lambda hlambda archimedeanTest weilTest⟩

def toPackage
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (data : S2B1TraceScaleAnalyticExclusionConstructorInput A W) :
    S2B1TraceScaleAnalyticExclusionPackage A W where
  supportSquareMainTermEqualsQWLambdaAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact
      row.supportSquareMainTermEqualsQWLambda
  rankZeroModeChannelClassifiedAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.rankZeroModeChannelClassified
  rankZeroModeChannelClassifiedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact
      ⟨hlambda, row.rankZeroModeChannelClassifiedHolds⟩
  noStripPostQRemainderRankPoleClassifiedAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.noStripPostQRemainderRankPoleClassified
  noStripPostQRemainderRankPoleClassifiedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact
      ⟨hlambda, row.noStripPostQRemainderRankPoleClassifiedHolds⟩
  endpointStripBulkClassifiedIntoCdefAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.endpointStripBulkClassifiedIntoCdef
  endpointStripBulkClassifiedIntoCdefAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact
      ⟨hlambda, row.endpointStripBulkClassifiedIntoCdefHolds⟩
  endpointStripBoundaryTermsClassifiedAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.endpointStripBoundaryTermsClassified
  endpointStripBoundaryTermsClassifiedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact
      ⟨hlambda, row.endpointStripBoundaryTermsClassifiedHolds⟩
  sourceSeriesTailClassifiedIntoCdefAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.sourceSeriesTailClassifiedIntoCdef
  sourceSeriesTailClassifiedIntoCdefAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact
      ⟨hlambda, row.sourceSeriesTailClassifiedIntoCdefHolds⟩
  cdefExhaustionOwnsEndpointStripAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.cdefExhaustionOwnsEndpointStrip
  cdefExhaustionOwnsEndpointStripAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact
      ⟨hlambda, row.cdefExhaustionOwnsEndpointStripHolds⟩
  noExtraBulkScaleTermExcludedAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
        row.noExtraBulkScaleTermExcluded
  noExtraBulkScaleTermExcludedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    let row := data.fixedTuple lambda hlambda archimedeanTest weilTest
    exact
      ⟨hlambda, row.noExtraBulkScaleTermExcludedHolds⟩
  finitePartSourceScalarDataAt :=
    fun lambda hlambda archimedeanTest weilTest =>
      (data.finitePartSourceNormalFormData
        lambda hlambda archimedeanTest weilTest).sourceScalars
  finitePartNormalizationFixedAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    exact
      (data.finitePartSourceNormalFormData
        lambda hlambda archimedeanTest weilTest).finitePartNormalizationFixedHolds
  noSubtractedFinitePartTermAtHolds := by
    intro lambda hlambda archimedeanTest weilTest
    exact
      (data.finitePartSourceNormalFormData
        lambda hlambda archimedeanTest weilTest).noSubtractedFinitePartTermHolds

end S2B1TraceScaleAnalyticExclusionConstructorInput

namespace S2B1TraceScaleAnalyticExclusionPackage

def toNoBulkRows
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (pkg : S2B1TraceScaleAnalyticExclusionPackage A W)
    (ordinary :
      ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A)
    (traceSquare :
      ArchimedeanTraceSymbols.TraceSquareStatement A)
    (qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W)
    (poleNormalization : WeilFormSymbols.PoleNormalizationStatement W) :
    S2B1TraceScaleNoBulkRows A W :=
  pkg.toTermLedgerRows.toNoBulkRows
    ordinary traceSquare qwLambdaFormula poleNormalization

def noBulkStatement
    {A : ArchimedeanTraceSymbols} {W : WeilFormSymbols}
    (pkg : S2B1TraceScaleAnalyticExclusionPackage A W)
    (ordinary :
      ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement A)
    (traceSquare :
      ArchimedeanTraceSymbols.TraceSquareStatement A)
    (qwLambdaFormula : WeilFormSymbols.QWLambdaFormulaStatement W)
    (poleNormalization : WeilFormSymbols.PoleNormalizationStatement W) :
    CC20CCMTraceScaleNoBulkStatement A W := by
  intro lambda hlambda archimedeanTest weilTest
  exact
    ⟨(pkg.toNoBulkRows ordinary traceSquare qwLambdaFormula
      poleNormalization).toWitness
        lambda hlambda archimedeanTest weilTest⟩

end S2B1TraceScaleAnalyticExclusionPackage

/--
The theorem-base staging package for Goal 2A.

It carries the source models whose laws discharge the compact theorem-base
records, plus the explicit CC20 finite-vanishing exit object still tracked for
Goal 5.
-/
structure SourceObjectTheoremBasePackage where
  ccm24Model : CCM24SourceModel
  ccm25Model : CCM25SourceModel
  cc20TraceModel : CC20TraceModel
  s2b1NormalizedSeed :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols
  s2b1NormalizedSeedArchimedeanSymbolsEq :
    (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      s2b1NormalizedSeed).archimedeanSymbols =
      cc20TraceModel.archimedeanSymbols
  s2b1RemainderRowsOutsideNoBulk :
    S2B1NormalizedCC20RemainderRowsOutsideNoBulk s2b1NormalizedSeed
  s2b1TraceScaleAnalyticExclusionConstructorInput :
    S2B1TraceScaleAnalyticExclusionConstructorInput
      cc20TraceModel.archimedeanSymbols ccm25Model.toWeilFormSymbols
  rhDefinitionBridge : RHDefinitionBridge
  cc20RHExitObjectPackage :
    CC20RHExitObjectPackage rhDefinitionBridge

/--
Constructor-facing source data for `SourceObjectTheoremBasePackage`.

This keeps the theorem-base models, normalized S2-B1 trace-scale rows, and
RH-exit bridge as separate source obligations before the compact package is
assembled.
-/
structure SourceObjectTheoremBaseConstructorInput where
  ccm24Model : CCM24SourceModel
  ccm25Model : CCM25SourceModel
  cc20TraceModel : CC20TraceModel
  s2b1NormalizedSeed :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols
  s2b1NormalizedSeedArchimedeanSymbolsEq :
    (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      s2b1NormalizedSeed).archimedeanSymbols =
      cc20TraceModel.archimedeanSymbols
  s2b1RemainderRowsOutsideNoBulk :
    S2B1NormalizedCC20RemainderRowsOutsideNoBulk s2b1NormalizedSeed
  s2b1TraceScaleAnalyticExclusionConstructorInput :
    S2B1TraceScaleAnalyticExclusionConstructorInput
      cc20TraceModel.archimedeanSymbols ccm25Model.toWeilFormSymbols
  rhDefinitionBridge : RHDefinitionBridge
  cc20RHExitObjectPackage :
    CC20RHExitObjectPackage rhDefinitionBridge

namespace SourceObjectTheoremBaseConstructorInput

def toPackage
    (data : SourceObjectTheoremBaseConstructorInput) :
    SourceObjectTheoremBasePackage where
  ccm24Model := data.ccm24Model
  ccm25Model := data.ccm25Model
  cc20TraceModel := data.cc20TraceModel
  s2b1NormalizedSeed := data.s2b1NormalizedSeed
  s2b1NormalizedSeedArchimedeanSymbolsEq :=
    data.s2b1NormalizedSeedArchimedeanSymbolsEq
  s2b1RemainderRowsOutsideNoBulk :=
    data.s2b1RemainderRowsOutsideNoBulk
  s2b1TraceScaleAnalyticExclusionConstructorInput :=
    data.s2b1TraceScaleAnalyticExclusionConstructorInput
  rhDefinitionBridge := data.rhDefinitionBridge
  cc20RHExitObjectPackage := data.cc20RHExitObjectPackage

end SourceObjectTheoremBaseConstructorInput

/--
Scalar CC20/common-test bridge rows.

The scalar remainder rows choose the CC20 trace test, while the finite-prime
common data choose the normalized common test.  These three rows are the
source-interface proof that both choices name the same source test in the
CC20 trace, trace-leg, and Mellin-leg positions.
-/
structure NormalizedScalarCC20CommonTestBridgeRows
    (base : SourceObjectTheoremBasePackage)
    (commonTest :
      SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols)
    (scalarSeed : CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (scalarRows : NormalizedScalarCC20RemainderRows scalarSeed) where
  sourceTraceTestCompatibility : Prop
  traceLegIsCommonTest : Prop
  mellinLegIsCommonTest : Prop

/--
Normalized route-ledger source rows.

This source-layer record deliberately avoids importing the route ledger type.
The development route layer interprets these three source rows as the concrete
`RouteLedgers` fields, while the theorem-base input remains the owner of the
rank, pole, and endpoint-strip `Cdef` clearing evidence.
-/
structure NormalizedRouteLedgerRows where
  rankKilled : Prop
  poleKilled : Prop
  cdefExhausts : Prop
  rankKilledHolds : rankKilled
  poleKilledHolds : poleKilled
  cdefExhaustsHolds : cdefExhausts

/--
Normalized source-object common-test bridge rows.

This record stays below `SourceObjectExpandedRows` to avoid an import cycle:
it names the common-test bridges directly against the base CCM25 Weil symbols,
the selected CCM24 object, and the selected CC20 trace object.
-/
structure NormalizedSourceObjectCommonTestBridgeRows
    (base : SourceObjectTheoremBasePackage)
    (commonTest :
      SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (cc20Trace : SourceObject.CC20TraceObjectPackage) where
  commonTestInvolution :
    SourceObject.CommonTestInvolutionBridge
      base.ccm25Model.toWeilFormSymbols commonTest
  ccm24Test_eq_commonTest :
    SourceObject.CCM24CommonTestBridge
      base.ccm25Model.toWeilFormSymbols commonTest ccm24
  cc20TraceTest_eq_commonTest :
    SourceObject.CC20CommonTestBridge
      base.ccm25Model.toWeilFormSymbols commonTest cc20Trace

/--
Normalized trace/read-off equalities at a fixed source cutoff.

The route-level `FullTraceReadOffEquality` and
`RestrictedTraceReadOffEquality` cannot live in the source package because
they mention route input wrappers.  This source record stores the same numeric
equalities directly against the source-object CC20 trace, common test, and
CCM25 Weil symbols.
-/
structure NormalizedSourceTraceReadOffEqualityRows
    (base : SourceObjectTheoremBasePackage)
    (commonTest :
      SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols)
    (cc20Trace : SourceObject.CC20TraceObjectPackage)
    (lambda : ℝ) where
  fullTraceReadOffEquality :
    cc20Trace.archimedeanSymbols.sourceNoDefectTrace
        cc20Trace.sourceTraceTest =
      base.ccm25Model.toWeilFormSymbols.qw
        commonTest.sourceTest commonTest.sourceTest
  restrictedTraceReadOffEquality :
    cc20Trace.archimedeanSymbols.supportSquareTrace
        cc20Trace.sourceTraceTest =
      base.ccm25Model.toWeilFormSymbols.qwLambda lambda
        commonTest.sourceTest commonTest.sourceTest

/--
Normalized theorem-base input with exact finite-prime source data.

The normalized route needs more than the compact theorem-base package: it also
needs fixed-lambda finite-prime certificates tied to the same CCM25 source
model.  Keeping both fields in one source-layer input prevents the development
skeleton from choosing an unrelated exact finite-prime package.
-/
structure NormalizedSourceObjectTheoremBaseInput where
  base : SourceObjectTheoremBasePackage
  finitePrimeExact :
    CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      base.ccm25Model.toWeilFormSymbols
  ccm24Object : SourceObject.CCM24SemilocalObjectPackage
  sourceObjectRHExit : SourceObject.CC20RHExitObjectPackage
  sourceObjectRHExitBridgeEq :
    sourceObjectRHExit.rhDefinitionBridge = base.rhDefinitionBridge
  commonTestBridgeRows :
    ∀ commonTest :
      SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols,
      ∀ cc20Trace : SourceObject.CC20TraceObjectPackage,
      NormalizedSourceObjectCommonTestBridgeRows
        base commonTest ccm24Object cc20Trace
  traceReadOffEqualityRows :
    ∀ (commonTest :
        SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols)
      (cc20Trace : SourceObject.CC20TraceObjectPackage)
      (lambda : ℝ),
      NormalizedSourceTraceReadOffEqualityRows
        base commonTest cc20Trace lambda
  scalarRemainderRows :
    ∀ scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      NormalizedScalarCC20RemainderRows scalarSeed
  scalarFinitePartSourceNormalFormData :
    ∀ scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
        ∀ archimedeanTest :
          (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              scalarSeed)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          S2B1FinitePartSourceNormalFormData
            (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
              (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
                scalarSeed)).archimedeanSymbols
            base.ccm25Model.toWeilFormSymbols
            lambda archimedeanTest weilTest
  scalarCommonTestBridgeRows :
    ∀ (commonTest :
        SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols)
      (scalarSeed :
        CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols),
      NormalizedScalarCC20CommonTestBridgeRows
        base commonTest scalarSeed (scalarRemainderRows scalarSeed)
  routeLedgerRows : NormalizedRouteLedgerRows

/--
Constructor-facing source data for the normalized theorem-base input.

This record has the same mathematical strength as
`NormalizedSourceObjectTheoremBaseInput`, but it is the formal input boundary
where the development skeleton should discharge fields one by one from source
theorems or concrete certificate data.  Keeping this constructor separate makes
the upstream proof obligations explicit instead of treating the normalized
theorem-base package as one opaque `sorry`.
-/
structure NormalizedSourceObjectCoreTheoremBaseData where
  base : SourceObjectTheoremBasePackage
  finitePrimeExact :
    CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      base.ccm25Model.toWeilFormSymbols

/--
Constructor boundary for the normalized core theorem-base data.

The theorem-base package and the exact finite-prime source package are split
so the development skeleton cannot hide both source obligations behind one
dependent record `sorry`.
-/
structure NormalizedSourceObjectCoreTheoremBaseConstructorInput where
  base : SourceObjectTheoremBasePackage
  finitePrimeExact :
    CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      base.ccm25Model.toWeilFormSymbols

namespace NormalizedSourceObjectCoreTheoremBaseConstructorInput

def toCoreData
    (data : NormalizedSourceObjectCoreTheoremBaseConstructorInput) :
    NormalizedSourceObjectCoreTheoremBaseData where
  base := data.base
  finitePrimeExact := data.finitePrimeExact

end NormalizedSourceObjectCoreTheoremBaseConstructorInput

structure NormalizedSourceObjectObjectData
    (core : NormalizedSourceObjectCoreTheoremBaseData) where
  ccm24Object : SourceObject.CCM24SemilocalObjectPackage
  sourceObjectRHExit : SourceObject.CC20RHExitObjectPackage
  sourceObjectRHExitBridgeEq :
    sourceObjectRHExit.rhDefinitionBridge = core.base.rhDefinitionBridge

/--
Constructor boundary for normalized source objects.

The CCM24 object, CC20 RH-exit object, and bridge equality are independent
source obligations and should remain inspectable before the object data record
is assembled.
-/
structure NormalizedSourceObjectObjectConstructorInput
    (core : NormalizedSourceObjectCoreTheoremBaseData) where
  ccm24Object : SourceObject.CCM24SemilocalObjectPackage
  sourceObjectRHExit : SourceObject.CC20RHExitObjectPackage
  sourceObjectRHExitBridgeEq :
    sourceObjectRHExit.rhDefinitionBridge = core.base.rhDefinitionBridge

namespace NormalizedSourceObjectObjectConstructorInput

def toObjectData
    {core : NormalizedSourceObjectCoreTheoremBaseData}
    (data : NormalizedSourceObjectObjectConstructorInput core) :
    NormalizedSourceObjectObjectData core where
  ccm24Object := data.ccm24Object
  sourceObjectRHExit := data.sourceObjectRHExit
  sourceObjectRHExitBridgeEq := data.sourceObjectRHExitBridgeEq

end NormalizedSourceObjectObjectConstructorInput

structure NormalizedSourceObjectBridgeReadOffData
    (core : NormalizedSourceObjectCoreTheoremBaseData)
    (objects : NormalizedSourceObjectObjectData core) where
  commonTestBridgeRows :
    ∀ commonTest :
      SourceObject.CommonTestObject core.base.ccm25Model.toWeilFormSymbols,
      ∀ cc20Trace : SourceObject.CC20TraceObjectPackage,
      NormalizedSourceObjectCommonTestBridgeRows
        core.base commonTest objects.ccm24Object cc20Trace
  traceReadOffEqualityRows :
    ∀ (commonTest :
        SourceObject.CommonTestObject core.base.ccm25Model.toWeilFormSymbols)
      (cc20Trace : SourceObject.CC20TraceObjectPackage)
      (lambda : ℝ),
      NormalizedSourceTraceReadOffEqualityRows
        core.base commonTest cc20Trace lambda

/--
Constructor boundary for normalized bridge and read-off rows.

Common-test identification and numeric trace read-off equalities are different
source obligations, so this constructor keeps them as separate fields before
the dependent bridge/read-off record is assembled.
-/
structure NormalizedSourceObjectBridgeReadOffConstructorInput
    (core : NormalizedSourceObjectCoreTheoremBaseData)
    (objects : NormalizedSourceObjectObjectData core) where
  commonTestBridgeRows :
    ∀ commonTest :
      SourceObject.CommonTestObject core.base.ccm25Model.toWeilFormSymbols,
      ∀ cc20Trace : SourceObject.CC20TraceObjectPackage,
      NormalizedSourceObjectCommonTestBridgeRows
        core.base commonTest objects.ccm24Object cc20Trace
  traceReadOffEqualityRows :
    ∀ (commonTest :
        SourceObject.CommonTestObject core.base.ccm25Model.toWeilFormSymbols)
      (cc20Trace : SourceObject.CC20TraceObjectPackage)
      (lambda : ℝ),
      NormalizedSourceTraceReadOffEqualityRows
        core.base commonTest cc20Trace lambda

namespace NormalizedSourceObjectBridgeReadOffConstructorInput

def toBridgeReadOffData
    {core : NormalizedSourceObjectCoreTheoremBaseData}
    {objects : NormalizedSourceObjectObjectData core}
    (data : NormalizedSourceObjectBridgeReadOffConstructorInput core objects) :
    NormalizedSourceObjectBridgeReadOffData core objects where
  commonTestBridgeRows := data.commonTestBridgeRows
  traceReadOffEqualityRows := data.traceReadOffEqualityRows

end NormalizedSourceObjectBridgeReadOffConstructorInput

structure NormalizedSourceObjectScalarRowsData
    (core : NormalizedSourceObjectCoreTheoremBaseData) where
  scalarRemainderRows :
    ∀ scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      NormalizedScalarCC20RemainderRows scalarSeed
  scalarFinitePartSourceNormalFormData :
    ∀ scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
        ∀ archimedeanTest :
          (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              scalarSeed)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          S2B1FinitePartSourceNormalFormData
            (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
              (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
                scalarSeed)).archimedeanSymbols
            core.base.ccm25Model.toWeilFormSymbols
            lambda archimedeanTest weilTest
  scalarCommonTestBridgeRows :
    ∀ (commonTest :
        SourceObject.CommonTestObject core.base.ccm25Model.toWeilFormSymbols)
      (scalarSeed :
        CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols),
      NormalizedScalarCC20CommonTestBridgeRows
        core.base commonTest scalarSeed (scalarRemainderRows scalarSeed)

/--
Constructor boundary for normalized scalar rows.

Scalar CC20 remainder data and scalar/common-test bridge rows have different
source provenance.  Keeping them split prevents the scalar lane from hiding
both behind a single provider.
-/
structure NormalizedSourceObjectScalarRowsConstructorInput
    (core : NormalizedSourceObjectCoreTheoremBaseData) where
  scalarRemainderRows :
    ∀ scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      NormalizedScalarCC20RemainderRows scalarSeed
  scalarFinitePartSourceNormalFormData :
    ∀ scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
        ∀ archimedeanTest :
          (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              scalarSeed)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          S2B1FinitePartSourceNormalFormData
            (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
              (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
                scalarSeed)).archimedeanSymbols
            core.base.ccm25Model.toWeilFormSymbols
            lambda archimedeanTest weilTest
  scalarCommonTestBridgeRows :
    ∀ (commonTest :
        SourceObject.CommonTestObject core.base.ccm25Model.toWeilFormSymbols)
      (scalarSeed :
        CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols),
      NormalizedScalarCC20CommonTestBridgeRows
        core.base commonTest scalarSeed (scalarRemainderRows scalarSeed)

namespace NormalizedSourceObjectScalarRowsConstructorInput

def toScalarRowsData
    {core : NormalizedSourceObjectCoreTheoremBaseData}
    (data : NormalizedSourceObjectScalarRowsConstructorInput core) :
    NormalizedSourceObjectScalarRowsData core where
  scalarRemainderRows := data.scalarRemainderRows
  scalarFinitePartSourceNormalFormData :=
    data.scalarFinitePartSourceNormalFormData
  scalarCommonTestBridgeRows := data.scalarCommonTestBridgeRows

end NormalizedSourceObjectScalarRowsConstructorInput

structure NormalizedSourceObjectLedgerRowsData where
  routeLedgerRows : NormalizedRouteLedgerRows

/--
Constructor boundary for normalized route-ledger rows.

The rank, pole, and endpoint-strip `Cdef` rows are separate source obligations.
This constructor keeps each row named before the compact
`NormalizedRouteLedgerRows` compatibility record is built.
-/
structure NormalizedSourceObjectLedgerRowsConstructorInput where
  rankKilled : Prop
  poleKilled : Prop
  cdefExhausts : Prop
  rankKilledHolds : rankKilled
  poleKilledHolds : poleKilled
  cdefExhaustsHolds : cdefExhausts

namespace NormalizedSourceObjectLedgerRowsConstructorInput

def toLedgerRowsData
    (data : NormalizedSourceObjectLedgerRowsConstructorInput) :
    NormalizedSourceObjectLedgerRowsData where
  routeLedgerRows :=
    { rankKilled := data.rankKilled
      poleKilled := data.poleKilled
      cdefExhausts := data.cdefExhausts
      rankKilledHolds := data.rankKilledHolds
      poleKilledHolds := data.poleKilledHolds
      cdefExhaustsHolds := data.cdefExhaustsHolds }

end NormalizedSourceObjectLedgerRowsConstructorInput

structure NormalizedSourceObjectTheoremBaseConstructorInput where
  core : NormalizedSourceObjectCoreTheoremBaseData
  objects : NormalizedSourceObjectObjectData core
  bridgeReadOff : NormalizedSourceObjectBridgeReadOffData core objects
  scalarRows : NormalizedSourceObjectScalarRowsData core
  ledgerRows : NormalizedSourceObjectLedgerRowsData

namespace NormalizedSourceObjectTheoremBaseConstructorInput

def toInput
    (data : NormalizedSourceObjectTheoremBaseConstructorInput) :
    NormalizedSourceObjectTheoremBaseInput where
  base := data.core.base
  finitePrimeExact := data.core.finitePrimeExact
  ccm24Object := data.objects.ccm24Object
  sourceObjectRHExit := data.objects.sourceObjectRHExit
  sourceObjectRHExitBridgeEq := data.objects.sourceObjectRHExitBridgeEq
  commonTestBridgeRows := data.bridgeReadOff.commonTestBridgeRows
  traceReadOffEqualityRows := data.bridgeReadOff.traceReadOffEqualityRows
  scalarRemainderRows := data.scalarRows.scalarRemainderRows
  scalarFinitePartSourceNormalFormData :=
    data.scalarRows.scalarFinitePartSourceNormalFormData
  scalarCommonTestBridgeRows := data.scalarRows.scalarCommonTestBridgeRows
  routeLedgerRows := data.ledgerRows.routeLedgerRows

end NormalizedSourceObjectTheoremBaseConstructorInput

namespace NormalizedSourceObjectTheoremBaseInput

def commonTestFunction
    (input : NormalizedSourceObjectTheoremBaseInput) : TestFunction :=
  input.finitePrimeExact.commonTestFunction

def sourceObjectCCM24
    (input : NormalizedSourceObjectTheoremBaseInput) :
    SourceObject.CCM24SemilocalObjectPackage :=
  input.ccm24Object

def sourceObjectCC20RHExit
    (input : NormalizedSourceObjectTheoremBaseInput) :
    SourceObject.CC20RHExitObjectPackage :=
  input.sourceObjectRHExit

theorem sourceObjectCC20RHExitBridgeEq
    (input : NormalizedSourceObjectTheoremBaseInput) :
    input.sourceObjectRHExit.rhDefinitionBridge =
      input.base.rhDefinitionBridge :=
  input.sourceObjectRHExitBridgeEq

def sourceObjectCommonTestBridgeRows
    (input : NormalizedSourceObjectTheoremBaseInput)
    (commonTest :
      SourceObject.CommonTestObject
        input.base.ccm25Model.toWeilFormSymbols)
    (cc20Trace : SourceObject.CC20TraceObjectPackage) :
    NormalizedSourceObjectCommonTestBridgeRows
      input.base commonTest input.ccm24Object cc20Trace :=
  input.commonTestBridgeRows commonTest cc20Trace

def sourceTraceReadOffEqualityRows
    (input : NormalizedSourceObjectTheoremBaseInput)
    (commonTest :
      SourceObject.CommonTestObject
        input.base.ccm25Model.toWeilFormSymbols)
    (cc20Trace : SourceObject.CC20TraceObjectPackage)
    (lambda : ℝ) :
    NormalizedSourceTraceReadOffEqualityRows
      input.base commonTest cc20Trace lambda :=
  input.traceReadOffEqualityRows commonTest cc20Trace lambda

def commonFinitePrimeData
    (input : NormalizedSourceObjectTheoremBaseInput) :
    CCM25Concrete.FinitePrimeSourceData.FinitePrimeArithmeticSourceData
      input.base.ccm25Model.toWeilFormSymbols
      (CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        input.base.ccm25Model.toWeilFormSymbols
        input.commonTestFunction) :=
  input.finitePrimeExact.finitePrimeData

def fixedLambdaArithmeticCertificatesForAllTests
    (input : NormalizedSourceObjectTheoremBaseInput) :
    CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticCertificatesForAllTests
      input.base.ccm25Model.toWeilFormSymbols :=
  CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticCertificatesForAllTests
    input.finitePrimeExact

def fixedLambdaArithmeticSourceTestCertificatesForAllTests
    (input : NormalizedSourceObjectTheoremBaseInput) :
    CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      input.base.ccm25Model.toWeilFormSymbols :=
  CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
    input.finitePrimeExact

theorem commonPairSourceTest
    (input : NormalizedSourceObjectTheoremBaseInput) :
    (input.commonFinitePrimeData.selector.sourceTest
        input.commonTestFunction input.commonTestFunction) =
      (CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        input.base.ccm25Model.toWeilFormSymbols
        input.commonTestFunction).toSourceTestEvaluationInterface :=
  CCM25Concrete.FinitePrimeSourceData.commonPairSourceTest
    input.finitePrimeExact

def scalarCC20RemainderRows
    (input : NormalizedSourceObjectTheoremBaseInput)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols) :
    NormalizedScalarCC20RemainderRows scalarSeed :=
  input.scalarRemainderRows scalarSeed

def scalarFinitePartSourceNormalFormDataAt
    (input : NormalizedSourceObjectTheoremBaseInput)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FinitePartSourceNormalFormData
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)).archimedeanSymbols
      input.base.ccm25Model.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  input.scalarFinitePartSourceNormalFormData
    scalarSeed lambda hlambda archimedeanTest weilTest

def scalarCC20RemainderData
    (input : NormalizedSourceObjectTheoremBaseInput)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols) :
    CC20Concrete.TraceScale.CC20TracePackageRemainderData
      (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        scalarSeed) :=
  (input.scalarCC20RemainderRows scalarSeed).toRemainderData

def scalarCC20CommonTestBridgeRows
    (input : NormalizedSourceObjectTheoremBaseInput)
    (commonTest :
      SourceObject.CommonTestObject
        input.base.ccm25Model.toWeilFormSymbols)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols) :
    NormalizedScalarCC20CommonTestBridgeRows
      input.base commonTest scalarSeed
      (input.scalarCC20RemainderRows scalarSeed) :=
  input.scalarCommonTestBridgeRows commonTest scalarSeed

def normalizedRouteLedgerRows
    (input : NormalizedSourceObjectTheoremBaseInput) :
    NormalizedRouteLedgerRows :=
  input.routeLedgerRows

end NormalizedSourceObjectTheoremBaseInput

namespace SourceObjectTheoremBasePackage

def toCCM24TheoremBase
    (pkg : SourceObjectTheoremBasePackage) : CCM24TheoremBase :=
  CCM24TheoremBase.discharged pkg.ccm24Model

def toCCM25TheoremBase
    (pkg : SourceObjectTheoremBasePackage) : CCM25TheoremBase :=
  CCM25TheoremBase.discharged pkg.ccm25Model

def toCC20TheoremBase
    (pkg : SourceObjectTheoremBasePackage) : CC20TheoremBase :=
  CC20TheoremBase.dischargedTraceBase
    pkg.cc20TraceModel pkg.cc20RHExitObjectPackage

def toSourceTheoremBase
    (pkg : SourceObjectTheoremBasePackage) : SourceTheoremBase :=
  SourceTheoremBase.dischargedTraceBase
    pkg.ccm24Model pkg.ccm25Model pkg.cc20TraceModel
    pkg.cc20RHExitObjectPackage

def toCCM24Interface
    (pkg : SourceObjectTheoremBasePackage) : CCM24Interface :=
  pkg.toCCM24TheoremBase.toInterface

def toCCM25Interface
    (pkg : SourceObjectTheoremBasePackage) : CCM25Interface :=
  pkg.toCCM25TheoremBase.toInterface

def toCC20Interface
    (pkg : SourceObjectTheoremBasePackage) : CC20Interface :=
  pkg.toCC20TheoremBase.toInterface

def toArchimedeanTraceSymbols
    (pkg : SourceObjectTheoremBasePackage) : ArchimedeanTraceSymbols :=
  pkg.cc20TraceModel.archimedeanSymbols

def toWeilFormSymbols
    (pkg : SourceObjectTheoremBasePackage) : WeilFormSymbols :=
  pkg.ccm25Model.toWeilFormSymbols

def s2b1CCM25QWLambdaFormula
    (pkg : SourceObjectTheoremBasePackage) :
    WeilFormSymbols.QWLambdaFormulaStatement pkg.toWeilFormSymbols :=
  pkg.toCCM25TheoremBase.qwLambdaFormula

def s2b1CCM25PoleNormalization
    (pkg : SourceObjectTheoremBasePackage) :
    WeilFormSymbols.PoleNormalizationStatement pkg.toWeilFormSymbols :=
  pkg.toCCM25TheoremBase.poleNormalization

def s2b1TraceScaleAnalyticExclusions
    (pkg : SourceObjectTheoremBasePackage) :
    S2B1TraceScaleAnalyticExclusionPackage
      pkg.cc20TraceModel.archimedeanSymbols pkg.ccm25Model.toWeilFormSymbols :=
  pkg.s2b1TraceScaleAnalyticExclusionConstructorInput.toPackage

def s2b1SupportSquareQWLambdaReadOffSourceData
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  S2B1TraceScaleAnalyticExclusionConstructorInput.supportSquareQWLambdaReadOffSourceData
    pkg.s2b1TraceScaleAnalyticExclusionConstructorInput
    lambda hlambda archimedeanTest weilTest

def s2b1RankZeroModeConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleRankZeroModeConstructorInput
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  S2B1TraceScaleAnalyticExclusionConstructorInput.rankZeroModeConstructorInput
    pkg.s2b1TraceScaleAnalyticExclusionConstructorInput
    lambda hlambda archimedeanTest weilTest

def s2b1NoStripRankPoleConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoStripRankPoleConstructorInput
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  S2B1TraceScaleAnalyticExclusionConstructorInput.noStripRankPoleConstructorInput
    pkg.s2b1TraceScaleAnalyticExclusionConstructorInput
    lambda hlambda archimedeanTest weilTest

def s2b1EndpointStripCdefConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleEndpointStripCdefConstructorInput
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  S2B1TraceScaleAnalyticExclusionConstructorInput.endpointStripCdefConstructorInput
    pkg.s2b1TraceScaleAnalyticExclusionConstructorInput
    lambda hlambda archimedeanTest weilTest

def s2b1NoExtraBulkConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoExtraBulkConstructorInput
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  S2B1TraceScaleAnalyticExclusionConstructorInput.noExtraBulkConstructorInput
    pkg.s2b1TraceScaleAnalyticExclusionConstructorInput
    lambda hlambda archimedeanTest weilTest

def s2b1FinitePartSourceNormalFormData
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FinitePartSourceNormalFormData
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  S2B1TraceScaleAnalyticExclusionConstructorInput.finitePartSourceNormalFormData
    pkg.s2b1TraceScaleAnalyticExclusionConstructorInput
    lambda hlambda archimedeanTest weilTest

def s2b1NoHiddenFinitePartSubtractionConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (pkg.s2b1FinitePartSourceNormalFormData
    lambda hlambda archimedeanTest weilTest).toNoHiddenFinitePartConstructorInput

def s2b1TraceScaleTermLedgerRows
    (pkg : SourceObjectTheoremBasePackage) :
    S2B1TraceScaleTermLedgerRows
      pkg.cc20TraceModel.archimedeanSymbols
      pkg.ccm25Model.toWeilFormSymbols :=
  pkg.s2b1TraceScaleAnalyticExclusionConstructorInput.toTermLedgerRows

def s2b1TraceScaleNoBulkRows
    (pkg : SourceObjectTheoremBasePackage) :
    S2B1TraceScaleNoBulkRows
      pkg.cc20TraceModel.archimedeanSymbols pkg.ccm25Model.toWeilFormSymbols :=
  pkg.s2b1TraceScaleAnalyticExclusionConstructorInput.toNoBulkRows
    pkg.cc20TraceModel.ordinaryTraceSupportSquare
    pkg.cc20TraceModel.archimedeanTraceSquare
    pkg.s2b1CCM25QWLambdaFormula
    pkg.s2b1CCM25PoleNormalization

def s2b1TraceScaleNoBulkStatement
    (pkg : SourceObjectTheoremBasePackage) :
    CC20CCMTraceScaleNoBulkStatement
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols :=
  pkg.s2b1TraceScaleAnalyticExclusionConstructorInput.noBulkStatement
    pkg.cc20TraceModel.ordinaryTraceSupportSquare
    pkg.cc20TraceModel.archimedeanTraceSquare
    pkg.s2b1CCM25QWLambdaFormula
    pkg.s2b1CCM25PoleNormalization

def s2b1NormalizedSeedBaseArchimedeanTest
    (pkg : SourceObjectTheoremBasePackage)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test) :
    pkg.toArchimedeanTraceSymbols.Test :=
  cast
    (congrArg ArchimedeanTraceSymbols.Test
      pkg.s2b1NormalizedSeedArchimedeanSymbolsEq)
    archimedeanTest

def s2b1NormalizedSeedSupportSquareQWLambdaReadOffSourceData
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData.transportArchimedean
    pkg.s2b1NormalizedSeedArchimedeanSymbolsEq.symm
    archimedeanTest
    (pkg.s2b1SupportSquareQWLambdaReadOffSourceData
      lambda hlambda
      (pkg.s2b1NormalizedSeedBaseArchimedeanTest archimedeanTest)
      weilTest)

def s2b1NormalizedSeedSupportSquareQWLambdaRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleSupportSquareQWLambdaRow
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  (pkg.s2b1NormalizedSeedSupportSquareQWLambdaReadOffSourceData
    lambda hlambda archimedeanTest weilTest).toRow

theorem s2b1NormalizedSeedSupportSquareMainTermEqualsQWLambda
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      pkg.s2b1NormalizedSeed).archimedeanSymbols.supportSquareTrace
        archimedeanTest =
      pkg.ccm25Model.toWeilFormSymbols.qwLambda lambda weilTest weilTest :=
  (pkg.s2b1NormalizedSeedSupportSquareQWLambdaRow
    lambda hlambda archimedeanTest weilTest).supportSquareMainTermEqualsQWLambda

def s2b1NormalizedSeedRankZeroModeConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleRankZeroModeConstructorInput
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  S2B1FixedTupleRankZeroModeConstructorInput.transportArchimedean
    pkg.s2b1NormalizedSeedArchimedeanSymbolsEq.symm
    archimedeanTest
    (pkg.s2b1RankZeroModeConstructorInput
      lambda hlambda
      (pkg.s2b1NormalizedSeedBaseArchimedeanTest archimedeanTest)
      weilTest)

def s2b1NormalizedSeedNoStripRankPoleConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoStripRankPoleConstructorInput
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  S2B1FixedTupleNoStripRankPoleConstructorInput.transportArchimedean
    pkg.s2b1NormalizedSeedArchimedeanSymbolsEq.symm
    archimedeanTest
    (pkg.s2b1NoStripRankPoleConstructorInput
      lambda hlambda
      (pkg.s2b1NormalizedSeedBaseArchimedeanTest archimedeanTest)
      weilTest)

def s2b1NormalizedSeedEndpointStripCdefConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleEndpointStripCdefConstructorInput
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  S2B1FixedTupleEndpointStripCdefConstructorInput.transportArchimedean
    pkg.s2b1NormalizedSeedArchimedeanSymbolsEq.symm
    archimedeanTest
    (pkg.s2b1EndpointStripCdefConstructorInput
      lambda hlambda
      (pkg.s2b1NormalizedSeedBaseArchimedeanTest archimedeanTest)
      weilTest)

def s2b1NormalizedSeedNoExtraBulkConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoExtraBulkConstructorInput
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  S2B1FixedTupleNoExtraBulkConstructorInput.transportArchimedean
    pkg.s2b1NormalizedSeedArchimedeanSymbolsEq.symm
    archimedeanTest
    (pkg.s2b1NoExtraBulkConstructorInput
      lambda hlambda
      (pkg.s2b1NormalizedSeedBaseArchimedeanTest archimedeanTest)
      weilTest)

def s2b1NormalizedSeedNoHiddenFinitePartSubtractionConstructorInput
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput.transportArchimedean
    pkg.s2b1NormalizedSeedArchimedeanSymbolsEq.symm
    archimedeanTest
    (pkg.s2b1NoHiddenFinitePartSubtractionConstructorInput
      lambda hlambda
      (pkg.s2b1NormalizedSeedBaseArchimedeanTest archimedeanTest)
      weilTest)

def s2b1FixedTupleRankZeroModeRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleRankZeroModeRow
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (pkg.s2b1RankZeroModeConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1FixedTupleNoStripRankPoleRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoStripRankPoleRow
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (pkg.s2b1NoStripRankPoleConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1FixedTupleEndpointStripCdefRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleEndpointStripCdefRow
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (pkg.s2b1EndpointStripCdefConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1FixedTupleNoExtraBulkRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoExtraBulkRow
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (pkg.s2b1NoExtraBulkConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1FixedTupleNoHiddenFinitePartSubtractionRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (pkg.s2b1NoHiddenFinitePartSubtractionConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1FixedTupleAnalyticExclusion
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  { oneLtLambda := hlambda
    supportSquareQWLambdaRow :=
      (pkg.s2b1SupportSquareQWLambdaReadOffSourceData
        lambda hlambda archimedeanTest weilTest).toRow
    rankZeroModeRow :=
      pkg.s2b1FixedTupleRankZeroModeRow lambda hlambda archimedeanTest weilTest
    noStripRankPoleRow :=
      pkg.s2b1FixedTupleNoStripRankPoleRow lambda hlambda archimedeanTest weilTest
    endpointStripCdefRow :=
      pkg.s2b1FixedTupleEndpointStripCdefRow lambda hlambda archimedeanTest weilTest
    noExtraBulkRow :=
      pkg.s2b1FixedTupleNoExtraBulkRow lambda hlambda archimedeanTest weilTest
    noHiddenFinitePartSubtractionRow :=
      pkg.s2b1FixedTupleNoHiddenFinitePartSubtractionRow
        lambda hlambda archimedeanTest weilTest }

def s2b1FixedTupleNoBulkWitness
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest : pkg.toArchimedeanTraceSymbols.Test)
    (weilTest : TestFunction) :
    CC20CCMTraceScaleNoBulkWitness
      pkg.toArchimedeanTraceSymbols pkg.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (pkg.s2b1FixedTupleAnalyticExclusion
      lambda hlambda archimedeanTest weilTest).toWitness
    pkg.cc20TraceModel.ordinaryTraceSupportSquare
    pkg.cc20TraceModel.archimedeanTraceSquare
    pkg.s2b1CCM25QWLambdaFormula
    pkg.s2b1CCM25PoleNormalization

def s2b1NormalizedSeedRankZeroModeRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleRankZeroModeRow
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  (pkg.s2b1NormalizedSeedRankZeroModeConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1NormalizedSeedNoStripRankPoleRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoStripRankPoleRow
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  (pkg.s2b1NormalizedSeedNoStripRankPoleConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1NormalizedSeedEndpointStripCdefRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleEndpointStripCdefRow
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  (pkg.s2b1NormalizedSeedEndpointStripCdefConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1NormalizedSeedNoExtraBulkRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoExtraBulkRow
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  (pkg.s2b1NormalizedSeedNoExtraBulkConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1NormalizedSeedNoHiddenFinitePartSubtractionRow
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest :=
  (pkg.s2b1NormalizedSeedNoHiddenFinitePartSubtractionConstructorInput
    lambda hlambda archimedeanTest weilTest).toRow

def s2b1NormalizedSeedFixedTupleAnalyticExclusion
    (pkg : SourceObjectTheoremBasePackage)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols lambda archimedeanTest weilTest where
  oneLtLambda := hlambda
  supportSquareQWLambdaRow :=
    pkg.s2b1NormalizedSeedSupportSquareQWLambdaRow
      lambda hlambda archimedeanTest weilTest
  rankZeroModeRow :=
    pkg.s2b1NormalizedSeedRankZeroModeRow
      lambda hlambda archimedeanTest weilTest
  noStripRankPoleRow :=
    pkg.s2b1NormalizedSeedNoStripRankPoleRow
      lambda hlambda archimedeanTest weilTest
  endpointStripCdefRow :=
    pkg.s2b1NormalizedSeedEndpointStripCdefRow
      lambda hlambda archimedeanTest weilTest
  noExtraBulkRow :=
    pkg.s2b1NormalizedSeedNoExtraBulkRow
      lambda hlambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionRow :=
    pkg.s2b1NormalizedSeedNoHiddenFinitePartSubtractionRow
      lambda hlambda archimedeanTest weilTest

open CC20Concrete.TraceScale in
def s2b1NormalizedSeedOrdinaryTraceSupportSquareStatement
    (pkg : SourceObjectTheoremBasePackage) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols :=
  normalized_legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square
    pkg.s2b1NormalizedSeed

open CC20Concrete.TraceScale in
def s2b1NormalizedSeedTraceSquareStatement
    (pkg : SourceObjectTheoremBasePackage) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols :=
  normalized_legal_square_trace_scale_to_cc20_trace_model_trace_square
    pkg.s2b1NormalizedSeed

def s2b1NormalizedSeedTraceScaleNoBulkRows
    (pkg : SourceObjectTheoremBasePackage) :
    S2B1TraceScaleNoBulkRows
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        pkg.s2b1NormalizedSeed).archimedeanSymbols
      pkg.toWeilFormSymbols where
  noBulkScaleTermOutsideLedgerAt :=
    fun lambda archimedeanTest weilTest =>
      ∀ hlambda : 1 < lambda,
        (pkg.s2b1NormalizedSeedFixedTupleAnalyticExclusion
          lambda hlambda archimedeanTest
          weilTest).toWitness
            (pkg.s2b1NormalizedSeedOrdinaryTraceSupportSquareStatement)
            (pkg.s2b1NormalizedSeedTraceSquareStatement)
            pkg.s2b1CCM25QWLambdaFormula
            pkg.s2b1CCM25PoleNormalization
            |>.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtractionAt :=
    fun lambda archimedeanTest weilTest =>
      ∀ hlambda : 1 < lambda,
        (pkg.s2b1NormalizedSeedFixedTupleAnalyticExclusion
          lambda hlambda archimedeanTest
          weilTest).toWitness
            (pkg.s2b1NormalizedSeedOrdinaryTraceSupportSquareStatement)
            (pkg.s2b1NormalizedSeedTraceSquareStatement)
            pkg.s2b1CCM25QWLambdaFormula
            pkg.s2b1CCM25PoleNormalization
            |>.noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerAtHolds := by
    intro lambda hlambda archimedeanTest weilTest hcurrent
    exact
      (pkg.s2b1NormalizedSeedFixedTupleAnalyticExclusion
        lambda hcurrent archimedeanTest
        weilTest).toWitness
          (pkg.s2b1NormalizedSeedOrdinaryTraceSupportSquareStatement)
          (pkg.s2b1NormalizedSeedTraceSquareStatement)
          pkg.s2b1CCM25QWLambdaFormula
          pkg.s2b1CCM25PoleNormalization
          |>.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionAtHolds := by
    intro lambda hlambda archimedeanTest weilTest hcurrent
    exact
      (pkg.s2b1NormalizedSeedFixedTupleAnalyticExclusion
        lambda hcurrent archimedeanTest
        weilTest).toWitness
          (pkg.s2b1NormalizedSeedOrdinaryTraceSupportSquareStatement)
          (pkg.s2b1NormalizedSeedTraceSquareStatement)
          pkg.s2b1CCM25QWLambdaFormula
          pkg.s2b1CCM25PoleNormalization
          |>.noHiddenFinitePartSubtractionHolds

theorem toSourceTheoremBase_ccm24_eq
    (pkg : SourceObjectTheoremBasePackage) :
    pkg.toSourceTheoremBase.ccm24 = pkg.toCCM24TheoremBase :=
  rfl

theorem toSourceTheoremBase_ccm25_eq
    (pkg : SourceObjectTheoremBasePackage) :
    pkg.toSourceTheoremBase.ccm25 = pkg.toCCM25TheoremBase :=
  rfl

theorem toSourceTheoremBase_cc20_eq
    (pkg : SourceObjectTheoremBasePackage) :
    pkg.toSourceTheoremBase.cc20 = pkg.toCC20TheoremBase :=
  rfl

theorem toCCM24Interface_eq
    (pkg : SourceObjectTheoremBasePackage) :
    pkg.toCCM24Interface = pkg.toSourceTheoremBase.toCCM24Interface :=
  rfl

theorem toCCM25Interface_eq
    (pkg : SourceObjectTheoremBasePackage) :
    pkg.toCCM25Interface = pkg.toSourceTheoremBase.toCCM25Interface :=
  rfl

theorem toCC20Interface_eq
    (pkg : SourceObjectTheoremBasePackage) :
    pkg.toCC20Interface = pkg.toSourceTheoremBase.toCC20Interface :=
  rfl

end SourceObjectTheoremBasePackage

end Source
end ConnesWeilRH
