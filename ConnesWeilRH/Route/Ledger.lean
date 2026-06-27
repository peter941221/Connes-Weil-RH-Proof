/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.AdmissibleWindow

/-!
# Ledger predicates

These predicates isolate the rank, pole, and `Cdef` terms that must be killed or
exhausted before the RH exit step.
-/

namespace ConnesWeilRH
namespace Route

def LedgersCleared (L : RouteLedgers) : Prop :=
  L.rankKilled ∧ L.poleKilled ∧ L.cdefExhausts

def RankRepairToZeroModeLedger
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs)
    (L : RouteLedgers) : Prop :=
  L.rankKilled

def PoleLedgerSupportedOnlyAtTateDirections
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs)
    (L : RouteLedgers) : Prop :=
  L.poleKilled

def EndpointStripNormalForm
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs)
    (L : RouteLedgers) : Prop :=
  L.cdefExhausts

def EndpointStripTraceNormBound
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs)
    (L : RouteLedgers) : Prop :=
  L.cdefExhausts

def QEndpointStripStability
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs)
    (L : RouteLedgers) : Prop :=
  L.cdefExhausts

def CdefGraphComparison
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs)
    (L : RouteLedgers) : Prop :=
  L.cdefExhausts

def FixedTestCdefExhaustion
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs)
    (L : RouteLedgers) : Prop :=
  L.cdefExhausts

structure CdefNormFormula
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) where
  endpointStripNormalForm : EndpointStripNormalForm inputs g L
  endpointStripTraceNormBound : EndpointStripTraceNormBound inputs g L
  qEndpointStripStability : QEndpointStripStability inputs g L
  cdefGraphComparison : CdefGraphComparison inputs g L
  fixedTestCdefExhaustion : FixedTestCdefExhaustion inputs g L

structure SourceBackedLedgers
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) where
  rankRepairToZeroMode : RankRepairToZeroModeLedger inputs g L
  poleLedgerSupportedOnlyAtTateDirections :
    PoleLedgerSupportedOnlyAtTateDirections inputs g L
  cdefNormFormula : CdefNormFormula inputs g L
  rankKilledBridge :
    (Source.ccm24BoundedComparison inputs.ccm24.semilocalSymbols).Holds →
      (Source.cc20SignsAndNormalizations inputs.cc20.archimedeanSymbols).Holds →
        RankRepairToZeroModeLedger inputs g L → L.rankKilled
  poleKilledBridge :
    (Source.ccm25PoleNormalization inputs.ccm25.weilSymbols).Holds →
      PoleLedgerSupportedOnlyAtTateDirections inputs g L → L.poleKilled
  cdefExhaustsBridge :
    (Source.ccm24SoninComparison inputs.ccm24.semilocalSymbols).Holds →
      (Source.cc20MellinHalfDensityConvention
          inputs.cc20.archimedeanSymbols).Holds →
        CdefNormFormula inputs g L → L.cdefExhausts

theorem rank_killed_of_ledgers_cleared
    {L : RouteLedgers} (h : LedgersCleared L) :
    L.rankKilled :=
  h.1

theorem pole_killed_of_ledgers_cleared
    {L : RouteLedgers} (h : LedgersCleared L) :
    L.poleKilled :=
  h.2.1

theorem cdef_exhausts_of_ledgers_cleared
    {L : RouteLedgers} (h : LedgersCleared L) :
    L.cdefExhausts :=
  h.2.2

theorem rank_killed_of_source_backed_ledgers
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    L.rankKilled :=
  h.rankKilledBridge inputs.ccm24.boundedComparison
    inputs.cc20.signsAndNormalizations h.rankRepairToZeroMode

theorem pole_killed_of_source_backed_ledgers
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    L.poleKilled :=
  h.poleKilledBridge inputs.ccm25.poleNormalization
    h.poleLedgerSupportedOnlyAtTateDirections

theorem cdef_exhausts_of_source_backed_ledgers
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    L.cdefExhausts :=
  h.cdefExhaustsBridge inputs.ccm24.soninComparison
    inputs.cc20.mellinHalfDensityConvention h.cdefNormFormula

theorem ledgers_cleared_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    LedgersCleared L :=
  ⟨rank_killed_of_source_backed_ledgers h,
    pole_killed_of_source_backed_ledgers h,
    cdef_exhausts_of_source_backed_ledgers h⟩

end Route
end ConnesWeilRH
