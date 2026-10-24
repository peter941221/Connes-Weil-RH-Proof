# 3074 — Route A owner identity and full-support bridge audit

Date: 2026-10-20

Status: `DIRECT-EQUALITY-NOT-WELL-TYPED`

The requested identity cannot currently be proved because the two sides are
different constructions with different quantifiers.

## Selected owner

The source definition is:

```text
selectedOwner base correction n
  = ofCompactLogTest
      (halfDensityShift
        ((convolutionIterate base n).convolution correction))
```

Here `correction` is an arbitrary `CompactLogTest` supplied by the residual
correction family, and `n` is an arbitrary orbit iteration index.

## Repaired owner

The record-2800 charge is built from two fixed coefficient vectors:

```text
record2678BaseCoefficient
record2680CorrectionCoefficient
```

and one fixed modulation vector:

```text
capturedModulations2584
```

The record is an interval certificate for four norm integrals over
`[0, record2675CellRight]`. It is not a `CompactLogTest` definition and it
does not contain `convolutionIterate`, the residual-family choice, or the
selected-owner parameter `n`.

Therefore the proposed equality

```text
selectedOwner = repaired-owner coefficient construction
```

is not a theorem about existing definitions. It requires a new construction
that defines a specific selected owner from the fixed coefficient vectors,
followed by a proof that the residual family returns exactly that construction.
The current residual family is classical-choice based and only exposes support
and finite Laplace interpolation; it does not expose coefficient identity.

## Full-support tail

The existing selected-owner tail lemmas control the Laplace transform under a
pointwise tail premise. The record-2800 certificate controls only the finite
interval `[0, record2675CellRight]`. No theorem currently combines them into a
signed residual inequality for the selected owner. The missing statement must
include an explicit tail term and the sign convention of the physical profile.

## Decision

Do not attempt to prove the requested equality by `simp`, `rfl`, or numerical
coefficient matching. The sound replacement is a new explicit owner package
whose fields include:

```text
owner identity for the fixed coefficient vectors
coefficient-cast and modulation equality
support/orientation equality
finite-window enclosure
full-support tail enclosure
signed residual assembly
```

Until that package exists, the 2800 charge cannot be applied to the selected
detector.

Correction (record 3078): the quantity named
`record2686RepairedOwnerTotal2800` is for one central cell only; it is not a
full finite-window charge. The all-cell stored-price ledger is record 2685.
Its exact arithmetic is proved below `knownError2109`, but its continuum
enclosure and the selected-owner full-support/tail transfer remain open.

Evidence:

- `ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean`
- `ConnesWeilRH/Dev/C1HealthyYoshidaCorrectionFamily.lean`
- `ConnesWeilRH/Dev/C1ChargeRestRecord2686Identity2800.lean`
- `ConnesWeilRH/Dev/C1RouteASelectedOwnerChargeBridge3073.lean`
