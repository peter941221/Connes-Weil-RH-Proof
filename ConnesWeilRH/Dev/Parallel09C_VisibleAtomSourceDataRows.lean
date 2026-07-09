/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.CC20RouteRealization

/-!
# 09C visible atom source-data rows scratch file

This lane isolates the source-data side of
`NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomSourceDataRowsCalibration`.
It does not edit the production route module.
-/

namespace ConnesWeilRH
namespace Route

open Source

/-- The 09C source-data certificate side unfolds to the atom normalization
stored in `data.finitePrimeData.certificateData` for the same `f`, `lambda`,
and cutoff proof. -/
theorem parallel09C_sourceDataCertificateAtoms_toNormalization
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) :
    let data := r.sourceBackedTest.finitePrimeSourceDataOwner
    let f := r.sourceBackedTest.weilTest
    let lambda := r.bridge.sourceTraceReadOff.lambda
    (((Source.CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
        data) f f).certificate lambda r.bridge.sourceTraceReadOff.oneLtLambda).atomsWithSourceTest.toNormalization =
      ((data.finitePrimeData.certificateData f f lambda
        r.bridge.sourceTraceReadOff.oneLtLambda).atoms).toNormalization := by
  rfl

/-- If the 09C row holds, the source-Weil-form visible atom owner is forced to
use the exact source-data certificate atom normalization.  This is the missing
object-identity condition to look for when auditing constructors. -/
theorem parallel09C_sourceAtoms_forced_eq_sourceDataCertificateAtoms
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration)
    (sourceAtoms :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomForSourceTestNormalizationCalibration
        hweil)
    (hsourceAtoms :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomSourceDataRowsCalibration
        hweil sourceAtoms)
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) :
    let data := r.sourceBackedTest.finitePrimeSourceDataOwner
    let f := r.sourceBackedTest.weilTest
    let lambda := r.bridge.sourceTraceReadOff.lambda
    ((data.finitePrimeData.certificateData f f lambda
      r.bridge.sourceTraceReadOff.oneLtLambda).atoms).toNormalization =
      (sourceAtoms.atomsWithSourceTest r).toNormalization := by
  let data := r.sourceBackedTest.finitePrimeSourceDataOwner
  let f := r.sourceBackedTest.weilTest
  let lambda := r.bridge.sourceTraceReadOff.lambda
  calc
    ((data.finitePrimeData.certificateData f f lambda
      r.bridge.sourceTraceReadOff.oneLtLambda).atoms).toNormalization =
        (((Source.CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
          data) f f).certificate lambda r.bridge.sourceTraceReadOff.oneLtLambda).atomsWithSourceTest.toNormalization := by
          simpa [data, f, lambda] using
            (parallel09C_sourceDataCertificateAtoms_toNormalization r).symm
    _ = (sourceAtoms.atomsWithSourceTest r).toNormalization := by
          simpa [
            NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomSourceDataRowsCalibration,
            data, f, lambda] using hsourceAtoms r

end Route
end ConnesWeilRH
