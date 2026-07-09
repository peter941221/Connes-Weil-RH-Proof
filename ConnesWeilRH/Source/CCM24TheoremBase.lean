/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM24
import ConnesWeilRH.Source.CCM24SourceModel

/-!
# CCM24 Lean theorem base

This module gives Goal 1 a Lean-checkable CCM24 theorem-base layer.  It does
not consume `SourceObligation.Holds`; the exported interface is built from
named theorem fields over concrete semilocal symbols.
-/

namespace ConnesWeilRH
namespace Source

/--
Negative boundary for Goal 1: CCM24's base model does not import post-`Q`
derivative, boundary, or tail transport as an automatic theorem.
-/
def CCM24AutomaticPostQTransportImported : Prop := False

theorem ccm24_no_automatic_post_q_transport :
    ¬ CCM24AutomaticPostQTransportImported := by
  intro h
  exact h

/-- Data-bearing Lean theorem base for the CCM24 source-interface row. -/
structure CCM24TheoremBase where
  semilocalSymbols : SemilocalModelSymbols
  canonicalSemilocalModel :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement semilocalSymbols
  supportTransport :
    SemilocalModelSymbols.SupportTransportStatement semilocalSymbols
  boundedComparison :
    SemilocalModelSymbols.BoundedComparisonStatement semilocalSymbols
  soninComparison :
    SemilocalModelSymbols.SoninComparisonStatement semilocalSymbols
  noAutomaticPostQTransport : ¬ CCM24AutomaticPostQTransportImported

namespace CCM24TheoremBase

def discharged (M : CCM24SourceModel) : CCM24TheoremBase where
  semilocalSymbols := M.semilocalSymbols
  canonicalSemilocalModel := ccm24_source_canonical_semilocal_model M
  supportTransport := ccm24_source_support_transport M
  boundedComparison := ccm24_source_bounded_comparison M
  soninComparison := ccm24_source_sonin_comparison M
  noAutomaticPostQTransport := ccm24_no_automatic_post_q_transport

def toInterface (h : CCM24TheoremBase) : CCM24Interface where
  semilocalSymbols := h.semilocalSymbols
  canonicalSemilocalModel := h.canonicalSemilocalModel
  supportTransport := h.supportTransport
  boundedComparison := h.boundedComparison
  soninComparison := h.soninComparison

end CCM24TheoremBase

end Source
end ConnesWeilRH
