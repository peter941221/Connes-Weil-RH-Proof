# Record 3261: Cell-2825 Support No-Go

## Result

The selected Route A owner at cell `2825` does not produce a physical
negative block. The center lies outside the shared family-8 support:

```text
|center| >= storedWidth 8^2
        |
        v
common_bump = 0
        |
        v
actual 22-family physical block = 0
```

The coefficient-phase aggregate remains strictly negative by record 3260, but
that sign is physically inactive at this cell because the common bump vanishes.
The proof reuses the exact shared-bump identity and preserves the same owner,
the same 22-family support, and the signed cancellation.

## Files

```text
ConnesWeilRH/Dev/C1RouteAConcreteOwnerCell2825PhysicalNegative3261.lean
ConnesWeilRH/Dev/C1RouteAConcreteOwnerCell2825PhysicalNegative3261Audit.lean
```

## Decision

Cell `2825` is rejected as a Route A producer candidate under the current
stored-width owner. Do not spend more phase-box or coefficient-phase work on
this cell unless the owner support or center definition changes.

This record does not prove a global Route A no-go. It only closes the named
cell-2825 mechanism and leaves the finite aggregate, full-line tail, C3'
signed budget, exact B5 readback, `producer_go`, `SourceRH`, and RH open.
