# 3072 — Route A selected-owner residual gate audit

Date: 2026-10-20

Status: `OPEN-OWNER-BRIDGE`

## Scope

This audit executes the Route A producer task after the selected-owner readback
was already formalized. It checks whether the existing repaired-owner charge
certificate can be consumed by the selected detector's signed residual gate.

## What is already proved

`C1RouteASelectedOwnerResidualReadback.lean` proves the exact same-owner
identity

```text
qw(selectedOwner.sourceTest)
  = -archimedeanTerm(selectedOwner.convolutionSquare)
    - selectedOwnerVisiblePrimeProfileWeightedSum(...)
```

under the registered triple-vanishing premise. This removes the opaque
`finitePrimeSum` presentation, but it does not establish the sign of the
right-hand side.

`C1RouteAProducerWired.lean` proves the producer consumer once a bound

```text
chargeRest <= knownError2109
```

is supplied.

`C1ChargeRestRecord2686Identity2800.lean` supplies that bound only from the
explicit identity

```text
chargeRest = record2686RepairedOwnerTotal2800
```

where the total is built from `record2678BaseCoefficient`,
`record2680CorrectionCoefficient`, `capturedModulations2584`, and the interval
`[0, record2675CellRight]`.

## Owner mismatch found

The selected-owner readback is parameterized by

```text
selectedOwner base (family.value y) n
```

and its physical quantity is the full bilateral profile of that owner's
`convolutionSquare`.

The repaired-owner total is a sum of four norm integrals for two fixed
coefficient records. The source currently has no theorem proving all of the
following simultaneously:

```text
selectedOwner base (family.value y) n = repaired-owner record
```

or an equivalent inequality connecting their full-support signed residuals,

```text
full selected-owner residual <= record2686RepairedOwnerTotal2800
```

with matching owner, coefficient casts, modulation vector, support domain,
orientation, and tail convention.

The existing record-2800 expression integrates only to
`record2675CellRight`; it is therefore not a full-support selected-owner
certificate by definition. The numerical value being below `knownError2109`
cannot repair this semantic gap.

## Binding next theorem

The next valid Route A theorem must have the following shape, or a strictly
stronger owner-identification theorem:

```text
theorem selectedOwner_chargeRest_le_knownError
    (howner : owner_identity_for_selected_detector)
    (hfull : full_support_residual_le_repaired_owner_total) :
    chargeRest <= knownError2109
```

Only after this theorem exists can
`a005_item5_producer_wired_repaired_owner_charge2802` consume the selected
detector. A theorem that merely restates the existing `chargeRest` equality,
or that matches the 30-family count, is insufficient.

## Decision

Do not promote the record-2800 charge into the selected-owner producer. The
correct next work item is the owner/coefficient/support bridge above. Until it
is proved, Route A has no producer GO and no RH conclusion.

## Correction (record 3078)

`record2686RepairedOwnerTotal2800` is the charge for the single central cell
`[0, record2675CellRight]`, whose endpoint is approximately `0.0016`; it is not
the full finite support charge. The all-cell numeric price is the exact
8192-cell ledger from record 2685, approximately `6.70596e6`, and its
continuum containment remains open. See
`docs/proofs/3078_routea_canonical_owner_and_grid_budget.md` for the corrected
scope and current interface.

## Evidence

- `ConnesWeilRH/Dev/C1RouteASelectedOwnerResidualReadback.lean`
- `ConnesWeilRH/Dev/C1RouteAProducerWired.lean`
- `ConnesWeilRH/Dev/C1RouteAProducerRepairedOwnerConsumer2802.lean`
- `ConnesWeilRH/Dev/C1ChargeRestRecord2686Identity2800.lean`
- `docs/proofs/2319_routea_producer_readback_no_go.md`
