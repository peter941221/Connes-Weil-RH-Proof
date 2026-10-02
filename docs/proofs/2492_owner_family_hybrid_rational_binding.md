# Record 2492: exact rational binding of the 2491 payload

The 2491 directed-MPFR artifact now carries binary64 RNDU payloads for all
640 cells, for both sigma signs, for both the L1 baseline and the hybrid
upper. `routea_owner_family_hybrid_table_2492.py` checks every hexadecimal
payload against its numerator/denominator ratio and generates
`C1RouteAOwnerFamilyHybridTable2492.lean` with exact `ℚ` literals and the
artifact SHA256.

The generated module is data only: it reconstructs stored endpoints but does
not prove that the MPFR computation encloses the analytic derivative. That
premise remains explicit and is the next producer-side obligation. The paired
Lean audit checks the two data accessors and is not an RH or producer claim.
