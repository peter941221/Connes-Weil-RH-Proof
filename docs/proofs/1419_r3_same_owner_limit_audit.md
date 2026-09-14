# 1419 — R3 same-owner limit audit

**Status:** R3 remains open. This record is a source-level audit of the
remaining analytic implication; it is not an RH claim and it does not add a
new axiom or a limit theorem by contract.

The healthy-`CompactLog` B5 consumer is the existing same-owner statement
`0 <= C1SameOwnerWeil.qw g` for the detector selected against a hypothetical
off-line zero. The purpose of R3 is to supply the positive-trace readback
needed by that consumer, without assuming either sign.

## 1. Exact target

For the fixed selected owner, Sonin scale, canonical finite-prime family, and
the two named bases, R3 must produce data of the following shape:

```text
remainder n -> 0
Re(trace_source(g8SourceCutoffPairData n)) - remainder n -> qw(owner.sourceTest)
```

The target is exactly the field pair in
`C1G8AdjointShearGram.lean:1016-1028`, not a generic positive trace and not a
different endpoint response.

## 2. What is already formal

The source audit finds the following genuine, non-circular facts.

| object | evidence | result |
| :-- | :-- | :-- |
| source cutoff | `C1G8AdjointShearGram.lean:499-577` | trace-class and positive at every cutoff |
| finite-cutoff ledger | `C1G8AdjointShearGram.lean:1297-1360` | exact four-channel trace identity |
| physical endpoint correction | `C1G8AdjointShearGram.lean:845-935` | G8 trace plus internal correction minus named complement |
| P1 endpoint handoff | `C1G8P1EndpointRemainder.lean:37-70` | one metric leakage cross is related to the source-band response and its remainder |
| P2 visible residual | `C1G8P2CanonicalResidual.lean:53-160` | projection response splits into visible Euler sum plus residual; a residual prefix has a limit |
| positivity consumer | `C1G8AdjointShearGram.lean:1033-1065` | the readback contract implies `0 <= qw` |

These are valuable prerequisites, but none of them identifies the limit of
the G8 source cutoff trace with `qw`.

## 3. The typed gap

There are currently three different layers, and the missing theorem must cross
all of them.

```text
G8 source cutoff trace
  = four positive cutoff channels
  = physical endpoint + internal correction - source complement
  ?-- metric/radial cutoff and endpoint transport --?
  = source-band response + visible Euler response + controlled residual
  ?-- endpoint formula and vanishing remainder --?
  = same-owner Weil value qw
```

The question marks are not cosmetic adapters. The existing declarations use
different operators or different cutoff sequences:

* `g8SourceCutoffPairData` is built from the literal full-boundary cutoff and
  `g8AdjointShearGram`.
* `sourceBandGramResponse` is the finite-S three-branch commutator owner.
* `projectionResponse` is the finite-S prolate/compression response, with
  `g8VisibleEulerResidual` defined as its residual.
* `tendsto_g8CompletedResidualPrefix_eq_routeTrace_sub_selectedSupport` only
  controls the completed residual prefix for `rootSandwichedBandResponse`; it
  does not mention `g8SourceCutoffPairData`.

Therefore the following tempting inference is invalid and remains unproved:

```text
positive G8 cutoff trace
  + P1 source-band formula
  + P2 residual-prefix limit
  => qw readback
```

The missing compatibility and limit equations have not been stated, let
alone proved.

## 4. Consequence for “finish R3”

R3 cannot honestly be marked GREEN by filling
`G8SameOwnerReadbackData` with an arbitrary remainder. Doing so would merely
store the desired limit. The plain-window predecessor is already formally
obstructed: its raw positive trace grows linearly and cannot converge to a
finite `qw` after a vanishing remainder. The G8 construction avoids that
specific obstruction by using a finite-S source compression, but the required
G8 transport theorem is still absent.

The correct R3 status is therefore:

```text
R3 finite-cutoff algebra       GREEN
R3 trace-class/positivity       GREEN
R3 channel ledger               GREEN
R3 metric-to-radial limit       OPEN
R3 endpoint-to-qw identification OPEN
R3 remainder convergence        OPEN
R3 readback data                NOT CONSTRUCTED
```

This is an analytic RH-level frontier, not a Lean API omission. A successful
proof of the missing readback would immediately feed the already formal
positive-trace consumer and the same-detector contradiction; that is why the
route is RH-reachable. It is not evidence that the missing proof is available.

## 5. The only admissible next attack

The next brick must be a genuine compatibility theorem, with no sign premise:

```text
R3-COMPAT:
  identify the limit of the actual G8 source-cutoff four-channel trace
  with the already-defined finite-S endpoint/readback owner, modulo one
  explicitly named scalar remainder.
```

Its falsifier is structural: if the limiting operator is not the same owner
as `sourceBandGramResponse`/`projectionResponse`, the current G8 readback
route is a route mismatch and must be closed rather than repaired by changing
the detector or its finite-prime family.

No numerical sign experiment can discharge R3-COMPAT. The proof must give an
operator identity or a norm/trace convergence theorem, followed by the
vanishing remainder and the exact `qw` endpoint identity.
