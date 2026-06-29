/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Theorem1

/-!
# Exhaustion step

This module names the passage from fixed-`S` restricted forms to the full Weil
positivity input required by the CC20 exit criterion.
-/

namespace ConnesWeilRH
namespace Route

structure FullWeilPositivity
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) where
  fixedSPositiveTraceReadOff : FixedSPositiveTraceReadOff inputs g
  tripleVanishing : g.test.tripleVanishing
  ledgersCleared : LedgersCleared L

def toWeilPositivityInput
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) :
    WeilPositivityInput where
  tripleVanishing := g.test.tripleVanishing
  fullWeilPositivity := FullWeilPositivity inputs g L

structure SourceBackedFullPositivity
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) where
  sourceTraceReadOff : SourceTraceReadOffData inputs g
  sourceBackedLedgers : SourceBackedLedgers inputs g L

def full_weil_positivity_of_source_backed_fixed_s
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (htrace : FixedSPositiveTraceReadOff inputs g)
    (hvanish : g.test.tripleVanishing)
    (hledger : SourceBackedLedgers inputs g L) :
    FullWeilPositivity inputs g L :=
  { fixedSPositiveTraceReadOff := htrace
    tripleVanishing := hvanish
    ledgersCleared := ledgers_cleared_of_source_backed hledger }

theorem cc20_trace_square_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceBackedFullPositivity inputs g L) :
    CC20TraceSquareReadOff inputs h.sourceTraceReadOff.archimedeanTest :=
  cc20_trace_square_of_source_trace_data h.sourceTraceReadOff

theorem ccm25_weil_form_read_off_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceBackedFullPositivity inputs g L) :
    CCM25WeilFormReadOff inputs g h.sourceTraceReadOff.lambda :=
  ccm25_weil_form_read_off_of_source_trace_data h.sourceTraceReadOff

def fixed_s_read_off_of_source_backed_full_positivity
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceBackedFullPositivity inputs g L) :
    FixedSPositiveTraceReadOff inputs g :=
  fixed_s_read_off_of_source_trace_data h.sourceTraceReadOff

def full_weil_positivity_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceBackedFullPositivity inputs g L) :
    FullWeilPositivity inputs g L :=
  full_weil_positivity_of_source_backed_fixed_s
    (fixed_s_read_off_of_source_backed_full_positivity h)
    (triple_vanishing_of_source_backed g)
    h.sourceBackedLedgers

def full_weil_positivity_input_holds
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : FullWeilPositivity inputs g L) :
    (toWeilPositivityInput inputs g L).fullWeilPositivity :=
  h

theorem triple_vanishing_input_holds
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : g.test.tripleVanishing) :
    (toWeilPositivityInput inputs g L).tripleVanishing :=
  h

end Route
end ConnesWeilRH
