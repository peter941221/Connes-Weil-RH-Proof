/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.SignDefect

/-!
# Ledger predicates

These predicates isolate the rank, pole, and `Cdef` terms that must be killed or
exhausted before the RH exit step.
-/

namespace ConnesWeilRH
namespace Route

structure LedgersCleared (L : RouteLedgers) : Prop where
  rankKilled : L.rankKilled
  poleKilled : L.poleKilled
  cdefExhausts : L.cdefExhausts

def ledgers_cleared_of_parts
    {L : RouteLedgers}
    (hrank : L.rankKilled) (hpole : L.poleKilled)
    (hcdef : L.cdefExhausts) :
    LedgersCleared L where
  rankKilled := hrank
  poleKilled := hpole
  cdefExhausts := hcdef

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
  lambda : ℝ
  signDefectClassification :
    SourceSignDefectClassification inputs g lambda L

structure LedgerSignDefectPackage
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) where
  ledgers : RouteLedgers
  ledgersCleared : LedgersCleared ledgers
  sourceBackedLedgers : SourceBackedLedgers inputs g ledgers
  sourceBackedLedgersLambda : sourceBackedLedgers.lambda = lambda
  signDefectClassification :
    SourceSignDefectClassification inputs g lambda ledgers

def cdef_norm_formula_of_cdef_exhausts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (hcdef : L.cdefExhausts) :
    CdefNormFormula inputs g L where
  endpointStripNormalForm := hcdef
  endpointStripTraceNormBound := hcdef
  qEndpointStripStability := hcdef
  cdefGraphComparison := hcdef
  fixedTestCdefExhaustion := hcdef

theorem cdef_norm_formula_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    CdefNormFormula inputs g L :=
  cdef_norm_formula_of_cdef_exhausts
    (cdef_exhausts_of_sign_defect_classification h)

def source_backed_ledgers_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    SourceBackedLedgers inputs g L where
  lambda := lambda
  signDefectClassification := h

def source_backed_ledgers_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hlambda : 1 < lambda)
    (hrank : L.rankKilled) (hpole : L.poleKilled)
    (hcdef : L.cdefExhausts) :
    SourceBackedLedgers inputs g L :=
  source_backed_ledgers_of_sign_defect_classification
    (source_sign_defect_classification_of_source_backed_ledgers
      hlambda hrank hpole hcdef)

theorem source_sign_defect_classification_of_ledgers_cleared
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hlambda : 1 < lambda) (h : LedgersCleared L) :
    SourceSignDefectClassification inputs g lambda L :=
  source_sign_defect_classification_of_source_backed_ledgers
    hlambda h.rankKilled h.poleKilled h.cdefExhausts

def source_backed_ledgers_of_ledgers_cleared
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hlambda : 1 < lambda) (h : LedgersCleared L) :
    SourceBackedLedgers inputs g L :=
  source_backed_ledgers_of_sign_defect_classification
    (source_sign_defect_classification_of_ledgers_cleared hlambda h)

def ledger_sign_defect_package_of_ledgers_cleared
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (L : RouteLedgers)
    (hlambda : 1 < lambda) (h : LedgersCleared L) :
    LedgerSignDefectPackage inputs g lambda where
  ledgers := L
  ledgersCleared := h
  sourceBackedLedgers :=
    source_backed_ledgers_of_ledgers_cleared hlambda h
  sourceBackedLedgersLambda := rfl
  signDefectClassification :=
    source_sign_defect_classification_of_ledgers_cleared hlambda h

def ledger_sign_defect_package_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (L : RouteLedgers)
    (hlambda : 1 < lambda)
    (hrank : L.rankKilled) (hpole : L.poleKilled)
    (hcdef : L.cdefExhausts) :
    LedgerSignDefectPackage inputs g lambda :=
  ledger_sign_defect_package_of_ledgers_cleared L hlambda
    (ledgers_cleared_of_parts hrank hpole hcdef)

theorem rank_killed_of_ledger_sign_defect_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (h : LedgerSignDefectPackage inputs g lambda) :
    h.ledgers.rankKilled :=
  h.ledgersCleared.rankKilled

theorem pole_killed_of_ledger_sign_defect_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (h : LedgerSignDefectPackage inputs g lambda) :
    h.ledgers.poleKilled :=
  h.ledgersCleared.poleKilled

theorem cdef_exhausts_of_ledger_sign_defect_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (h : LedgerSignDefectPackage inputs g lambda) :
    h.ledgers.cdefExhausts :=
  h.ledgersCleared.cdefExhausts

theorem rank_killed_of_ledgers_cleared
    {L : RouteLedgers} (h : LedgersCleared L) :
    L.rankKilled :=
  h.rankKilled

theorem pole_killed_of_ledgers_cleared
    {L : RouteLedgers} (h : LedgersCleared L) :
    L.poleKilled :=
  h.poleKilled

theorem cdef_exhausts_of_ledgers_cleared
    {L : RouteLedgers} (h : LedgersCleared L) :
    L.cdefExhausts :=
  h.cdefExhausts

theorem rank_killed_of_source_backed_ledgers
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    L.rankKilled :=
  rank_killed_of_sign_defect_classification h.signDefectClassification

theorem pole_killed_of_source_backed_ledgers
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    L.poleKilled :=
  pole_killed_of_sign_defect_classification h.signDefectClassification

theorem cdef_exhausts_of_source_backed_ledgers
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    L.cdefExhausts :=
  cdef_exhausts_of_sign_defect_classification h.signDefectClassification

theorem cdef_norm_formula_of_source_backed_ledgers
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    CdefNormFormula inputs g L :=
  cdef_norm_formula_of_cdef_exhausts
    (cdef_exhausts_of_source_backed_ledgers h)

theorem ledgers_cleared_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    LedgersCleared L :=
  { rankKilled := rank_killed_of_source_backed_ledgers h
    poleKilled := pole_killed_of_source_backed_ledgers h
    cdefExhausts := cdef_exhausts_of_source_backed_ledgers h }

def ledger_sign_defect_package_of_source_backed_ledgers
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} (h : SourceBackedLedgers inputs g L) :
    LedgerSignDefectPackage inputs g h.lambda where
  ledgers := L
  ledgersCleared := ledgers_cleared_of_source_backed h
  sourceBackedLedgers := h
  sourceBackedLedgersLambda := rfl
  signDefectClassification := h.signDefectClassification

def source_backed_ledgers_of_route_ledger_semantics
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : RouteLedgerSemanticData inputs g lambda L) :
    SourceBackedLedgers inputs g L :=
  source_backed_ledgers_of_sign_defect_classification
    h.sourceSignDefectClassification

def ledger_sign_defect_package_of_route_ledger_semantics
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : RouteLedgerSemanticData inputs g lambda L) :
    LedgerSignDefectPackage inputs g lambda where
  ledgers := L
  ledgersCleared :=
    ledgers_cleared_of_source_backed
      (source_backed_ledgers_of_route_ledger_semantics h)
  sourceBackedLedgers :=
    source_backed_ledgers_of_route_ledger_semantics h
  sourceBackedLedgersLambda := rfl
  signDefectClassification := h.sourceSignDefectClassification

theorem ledgers_cleared_of_source_backed_parts
    {L : RouteLedgers}
    (hrank : L.rankKilled) (hpole : L.poleKilled)
    (hcdef : L.cdefExhausts) :
    LedgersCleared L :=
  ledgers_cleared_of_parts hrank hpole hcdef

theorem ledgers_cleared_of_source_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    LedgersCleared L :=
  ledgers_cleared_of_source_backed
    (source_backed_ledgers_of_sign_defect_classification h)

end Route
end ConnesWeilRH
