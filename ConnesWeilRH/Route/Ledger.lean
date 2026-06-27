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

structure SourceBackedLedgers (inputs : RouteInputs) (L : RouteLedgers) where
  rankLedgerSource : Prop
  poleLedgerSource : Prop
  cdefLedgerSource : Prop
  rankLedgerSourceHolds : rankLedgerSource
  poleLedgerSourceHolds : poleLedgerSource
  cdefLedgerSourceHolds : cdefLedgerSource
  rankKilledBridge :
    (Source.ccm24BoundedComparison inputs.ccm24.semilocalSymbols).Holds →
      (Source.cc20SignsAndNormalizations inputs.cc20.archimedeanSymbols).Holds →
        rankLedgerSource → L.rankKilled
  poleKilledBridge :
    (Source.ccm25PoleNormalization inputs.ccm25.weilSymbols).Holds →
      poleLedgerSource → L.poleKilled
  cdefExhaustsBridge :
    (Source.ccm24SoninComparison inputs.ccm24.semilocalSymbols).Holds →
      (Source.cc20MellinHalfDensityConvention
          inputs.cc20.archimedeanSymbols).Holds →
        cdefLedgerSource → L.cdefExhausts

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
    {inputs : RouteInputs} {L : RouteLedgers}
    (h : SourceBackedLedgers inputs L) :
    L.rankKilled :=
  h.rankKilledBridge inputs.ccm24.boundedComparison
    inputs.cc20.signsAndNormalizations h.rankLedgerSourceHolds

theorem pole_killed_of_source_backed_ledgers
    {inputs : RouteInputs} {L : RouteLedgers}
    (h : SourceBackedLedgers inputs L) :
    L.poleKilled :=
  h.poleKilledBridge inputs.ccm25.poleNormalization h.poleLedgerSourceHolds

theorem cdef_exhausts_of_source_backed_ledgers
    {inputs : RouteInputs} {L : RouteLedgers}
    (h : SourceBackedLedgers inputs L) :
    L.cdefExhausts :=
  h.cdefExhaustsBridge inputs.ccm24.soninComparison
    inputs.cc20.mellinHalfDensityConvention h.cdefLedgerSourceHolds

theorem ledgers_cleared_of_source_backed
    {inputs : RouteInputs} {L : RouteLedgers}
    (h : SourceBackedLedgers inputs L) :
    LedgersCleared L :=
  ⟨rank_killed_of_source_backed_ledgers h,
    pole_killed_of_source_backed_ledgers h,
    cdef_exhausts_of_source_backed_ledgers h⟩

end Route
end ConnesWeilRH
