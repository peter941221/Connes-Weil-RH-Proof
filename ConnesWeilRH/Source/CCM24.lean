/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.ObjectDerivations

/-!
# CCM24 source interface

This file names the CCM24 inputs used by the Connes-Weil route. Phase 1 treats
these as explicit hypotheses, not hidden axioms.
-/

namespace ConnesWeilRH
namespace Source

variable (M : SemilocalModelSymbols)

def ccm24CanonicalSemilocalModel : SourceObligation where
  sourceKey := "CCM24"
  sourceFile := "mainc2m24fine.tex"
  lineRange := "237-253, 786-804"
  manuscriptRole :=
    "canonical fixed-S Hilbert model, V_S=M_S U_S, and Fourier grading"
  statement := SemilocalModelSymbols.CanonicalSemilocalModelStatement M

def ccm24SupportTransport : SourceObligation where
  sourceKey := "CCM24"
  sourceFile := "mainc2m24fine.tex"
  lineRange := "761-771, 983-1003"
  manuscriptRole :=
    "support and Fourier-support transport for Lemmas A and B"
  statement := SemilocalModelSymbols.SupportTransportStatement M

def ccm24BoundedComparison : SourceObligation where
  sourceKey := "CCM24"
  sourceFile := "mainc2m24fine.tex"
  lineRange := "806-823"
  manuscriptRole :=
    "bounded comparison map with bounded inverse"
  statement := SemilocalModelSymbols.BoundedComparisonStatement M

def ccm24SoninComparison : SourceObligation where
  sourceKey := "CCM24"
  sourceFile := "mainc2m24fine.tex"
  lineRange := "1050-1060"
  manuscriptRole :=
    "Sonin-space comparison for fixed support-window exhaustion"
  statement := SemilocalModelSymbols.SoninComparisonStatement M

structure CCM24Interface where
  semilocalSymbols : SemilocalModelSymbols
  canonicalSemilocalModel :
    (ccm24CanonicalSemilocalModel semilocalSymbols).Holds
  supportTransport : (ccm24SupportTransport semilocalSymbols).Holds
  boundedComparison : (ccm24BoundedComparison semilocalSymbols).Holds
  soninComparison : (ccm24SoninComparison semilocalSymbols).Holds

namespace CCM24Interface

def ofSourceObjectPackage
    (pkg : SourceObject.SourceObjectPackage) : CCM24Interface where
  semilocalSymbols := pkg.toSemilocalModelSymbols
  canonicalSemilocalModel :=
    SourceObject.SourceObjectPackage.provesCanonicalSemilocalModelStatement pkg
  supportTransport :=
    SourceObject.SourceObjectPackage.provesSupportTransportStatement pkg
  boundedComparison :=
    SourceObject.SourceObjectPackage.provesBoundedComparisonStatement pkg
  soninComparison :=
    SourceObject.SourceObjectPackage.provesSoninComparisonStatement pkg

end CCM24Interface

end Source
end ConnesWeilRH
