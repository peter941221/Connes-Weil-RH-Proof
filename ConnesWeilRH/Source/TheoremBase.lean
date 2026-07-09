/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM24TheoremBase
import ConnesWeilRH.Source.CCM25TheoremBase
import ConnesWeilRH.Source.CC20TheoremBase

/-!
# Combined source theorem base

This module combines the Goal 1 theorem bases for CCM24, CCM25, and CC20.  It
only exposes constructors for the compact source interfaces; it does not build
`SourceObjectPackage`, route front ends, `RouteCertificate`, or an
unconditional RH theorem.
-/

namespace ConnesWeilRH
namespace Source

structure SourceTheoremBase where
  ccm24 : CCM24TheoremBase
  ccm25 : CCM25TheoremBase
  cc20 : CC20TheoremBase

namespace SourceTheoremBase

def dischargedTraceBase
    (ccm24 : CCM24SourceModel)
    (ccm25 : CCM25SourceModel)
    (cc20 : CC20TraceModel)
    {B : RHDefinitionBridge}
    (rhExit : CC20RHExitObjectPackage B) : SourceTheoremBase where
  ccm24 := CCM24TheoremBase.discharged ccm24
  ccm25 := CCM25TheoremBase.discharged ccm25
  cc20 := CC20TheoremBase.dischargedTraceBase cc20 rhExit

def toCCM24Interface (h : SourceTheoremBase) : CCM24Interface :=
  h.ccm24.toInterface

def toCCM25Interface (h : SourceTheoremBase) : CCM25Interface :=
  h.ccm25.toInterface

def toCC20Interface (h : SourceTheoremBase) : CC20Interface :=
  h.cc20.toInterface

theorem toCCM24Interface_eq (h : SourceTheoremBase) :
    h.toCCM24Interface = h.ccm24.toInterface :=
  rfl

theorem toCCM25Interface_eq (h : SourceTheoremBase) :
    h.toCCM25Interface = h.ccm25.toInterface :=
  rfl

theorem toCC20Interface_eq (h : SourceTheoremBase) :
    h.toCC20Interface = h.cc20.toInterface :=
  rfl

end SourceTheoremBase

end Source
end ConnesWeilRH
