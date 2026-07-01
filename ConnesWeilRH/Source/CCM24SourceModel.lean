/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.Objects

/-!
# CCM24 source model

This module gives Goal 1B a source-facing model for the CCM24 fixed-`S`
semilocal row. The model carries the concrete semilocal symbols and the named
source laws needed by the theorem-base record. It does not import
`SourceObligation.Holds` or reviewer decisions.
-/

namespace ConnesWeilRH
namespace Source

/-- Source-facing CCM24 data for the fixed-`S` semilocal theorem base. -/
structure CCM24SourceModel where
  semilocalSymbols : SemilocalModelSymbols
  canonicalSemilocalModel :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement semilocalSymbols
  supportTransport :
    SemilocalModelSymbols.SupportTransportStatement semilocalSymbols
  boundedComparison :
    SemilocalModelSymbols.BoundedComparisonStatement semilocalSymbols
  soninComparison :
    SemilocalModelSymbols.SoninComparisonStatement semilocalSymbols

theorem ccm24_source_canonical_semilocal_model
    (M : CCM24SourceModel) :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement
      M.semilocalSymbols :=
  M.canonicalSemilocalModel

theorem ccm24_source_support_transport
    (M : CCM24SourceModel) :
    SemilocalModelSymbols.SupportTransportStatement M.semilocalSymbols :=
  M.supportTransport

theorem ccm24_source_bounded_comparison
    (M : CCM24SourceModel) :
    SemilocalModelSymbols.BoundedComparisonStatement M.semilocalSymbols :=
  M.boundedComparison

theorem ccm24_source_sonin_comparison
    (M : CCM24SourceModel) :
    SemilocalModelSymbols.SoninComparisonStatement M.semilocalSymbols :=
  M.soninComparison

def ccm24_source_model_of_semilocal_object
    (pkg : SourceObject.CCM24SemilocalObjectPackage) :
    CCM24SourceModel where
  semilocalSymbols := pkg.semilocalSymbols
  canonicalSemilocalModel := pkg.sourceCanonicalSemilocalModel
  supportTransport := pkg.sourceSupportAndFourierSupportTransport
  boundedComparison := pkg.sourceBoundedComparisonTraceClassTransport
  soninComparison := pkg.sourceFixedWindowSoninExhaustion

end Source
end ConnesWeilRH
