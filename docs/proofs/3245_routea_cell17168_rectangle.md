# 3245: Route A cell 17168 rectangle interface

Status
------

Lean-verified enclosure interface. This record does not prove a negative
cell value, the finite aggregate, the full-line tail, producer_go, SourceRH,
or RH.

What changed
------------

The earlier 3243 rectangle interface was tied to cell 16923. Record 3244
screening identified cell 17168 as the strongest negative Taylor-6 diagnostic
cell. Record 3245 reuses the already audited 3231 bump interval and 3236
phase construction at that coordinate.

The new module proves:

    bump rectangle membership
        -> phase rectangle membership
        -> family rectangle membership
        -> 30-family aggregate rectangle membership
        -> exact unweighted real-part upper

Files
-----

    ConnesWeilRH/Dev/C1RouteAConcreteOwnerCell17168Rect3245.lean
    ConnesWeilRH/Dev/C1RouteAConcreteOwnerCell17168Rect3245Audit.lean

Verification
------------

The source module and audit were built in a Linux-native WSL2 ext4 workspace.
The repository toolchain was checked as leanprover/lean4:v4.30.0 and Lean
4.30.0. The lake audit completed successfully and every new theorem depended
only on propext, Classical.choice, and Quot.sound.

Boundary
--------

The rectangle is still formed by multiplying each family separately and then
summing. Direct endpoint sign expansion was rejected separately in record
3246 because it exhausts the Lean simplifier. The next producer-facing object
must group coefficient-phase cancellation before applying a shared bump
envelope.
