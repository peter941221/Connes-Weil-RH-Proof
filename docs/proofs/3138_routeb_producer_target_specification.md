# Record 3138: Route-B producer target specification

Date: 2026-10-27.

Status: specification and interface boundary only. This record does not
claim a numerical gate, `fullWeilPositivity`, Producer GO, `SourceRH`, or RH.

## Problem restatement

The 3136 certificate contract checks that an exact-owner numerical artifact has
the fields needed for a signed gate-margin audit. Record 3137 fixes the exact
prime-index membership rule for the 3117 powered owner. Neither record yet
constructs the Lean proposition consumed by the CC20 exit.

The missing question is not whether a JSON margin looks positive. It is how
the same owner enters the existing Lean proposition:

```text
exact-owner certificate
        |
        v
same-owner analytic readback
        |
        v
FixedSPositiveTraceReadOff + triple vanishing + LedgersCleared
        |
        v
Route.FullWeilPositivity
        |
        v
Route.toWeilPositivityInput
        |
        v
input.fullWeilPositivity
        |
        v
CC20 Proposition C.1 -> SourceRH -> Mathlib RH
```

## Source-level evidence

The project code makes the consumer contract explicit:

- `ConnesWeilRH/Route/Exhaustion.lean:19` defines
  `Route.FullWeilPositivity` with exactly three fields:
  `fixedSPositiveTraceReadOff`, `tripleVanishing`, and `ledgersCleared`.
- `ConnesWeilRH/Route/Exhaustion.lean:26` maps that structure into
  `WeilPositivityInput.fullWeilPositivity`.
- `ConnesWeilRH/Route/Theorem1.lean:405` defines the fixed-`S` positive trace
  readout. It requires trace legality, test/quotient compatibility, support
  transport, the no-defect source readout, the CCM25 Weil-form readout, and a
  nonnegative positive trace.
- `ConnesWeilRH/Route/Ledger.lean:84` defines the ledger package. A cleared
  ledger must still be tied to the source sign-defect classification; it is
  not a free numerical remainder flag.
- `ConnesWeilRH/Source/CC20RHExit.lean:75` requires the concrete proposition
  `input.fullWeilPositivity` inside Proposition C.1 input data.
- `ConnesWeilRH/Route/RouteTheorem.lean:54` and `:71` carry the same field into
  the route-backed exit data. A positive scalar margin by itself has no field
  in this structure.

## Required producer theorem shape

The next admissible producer theorem must have the following logical shape.
The names are schematic; the fields must use the existing project types rather
than introducing parallel certificate types.

```text
theorem route_b_exact_owner_producer_go
    {inputs : RouteInputs}
    {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (owner : exact 3117 powered owner)
    (owner_readback : owner = g.weilTest / same-owner identity)
    (prime_index_readback : owner globalPrimeIndexSet = canonical set)
    (prime_power_completeness : exact owner sum = certified owner sum)
    (signed_residual : signed residual enclosure with both frequency signs)
    (continuum_gate : same-owner continuum gate margin is nonnegative)
    (htrace : FixedSPositiveTraceReadOff inputs g)
    (hvanish : g.test.tripleVanishing)
    (hledger : LedgersCleared L) :
    FullWeilPositivity inputs g L
```

The first five hypotheses are evidence used to prove the existing fields.
They are not substitutes for `htrace` or `hledger`. The final output must be
constructed by `full_weil_positivity_of_source_backed_fixed_s` or an equivalent
proof returning the same `FullWeilPositivity` type.

## Obligation matrix

```text
+------------------------------+----------------------+--------------------------+
| Obligation                   | Current record       | Consumer status          |
+------------------------------+----------------------+--------------------------+
| Exact powered owner          | 3137                 | Lean identity/readback   |
| Prime-index membership       | 3137                 | Canonical set fixed     |
| Certificate field semantics  | 3136 contract        | Structural only          |
| Both frequency signs         | 3136 contract        | No analytic proof yet   |
| Signed prime-power residual  | 3136 contract        | No completeness theorem  |
| Continuum gate margin        | 3136 contract        | No same-owner readback  |
| Fixed-S trace readout        | none                 | Required by Route       |
| Ledger defect clearance      | none                 | Required by Route       |
| `fullWeilPositivity`         | none                 | Required by CC20 C.1    |
| Producer GO / `SourceRH`     | none                 | Must remain unclaimed   |
+------------------------------+----------------------+--------------------------+
```

## Route-B disposition

Records 3117, 3134, and 3135 prove a same-owner negative-`qw` construction and
its gate rejection under the stated support and vanishing hypotheses. That is
falsification/no-go evidence: it blocks a gate for the constructed negative
owner. It is not a positivity producer and cannot be inverted into a positive
gate theorem.

Therefore the Route-B numerical manifest generator remains frozen. The next
Route-B code change is allowed only after a Lean theorem is identified for each
missing consumer field, especially `FixedSPositiveTraceReadOff` and
`LedgersCleared`. Until then, Route A remains the binding producer lane.

## Decision

Do not create an owner manifest merely to satisfy 3136. The correct next
implementation target is a proof-level bridge from a same-owner, signed,
continuum certificate to the existing fixed-`S` trace and ledger structures.
If that bridge cannot be stated without adding a new axiom, changing the owner,
or weakening the existing route types, the result must be recorded as a
producer no-go rather than hidden behind a certificate field.
