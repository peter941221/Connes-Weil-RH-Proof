/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.TheoremBase

/-!
# Source-object theorem-base staging package

Goal 2A collects the Goal 1B source models into a source-object staging layer.
This module does not build `SourceObjectPackage`, common-test data, route
front ends, `RouteCertificate`, or an unconditional RH theorem.
-/

namespace ConnesWeilRH
namespace Source

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
  rhDefinitionBridge : RHDefinitionBridge
  cc20RHExitObjectPackage :
    CC20RHExitObjectPackage rhDefinitionBridge

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
