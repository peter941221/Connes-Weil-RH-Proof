# G8 P1 finite-prime assembly (2026-09-11)

## Result

`C1G8P1FinitePrimeAssembly.lean` defines
`familyVisiblePrimePowerTerms` for every `FinitePrimePowerFamily`.  The
construction maps each owned natural prime-power term to the corresponding
`CCM24VisiblePrime` witness and retains the exponent and visible-place proofs.
The theorem
`familyVisiblePrimePowerTerms_natTerms_eq` proves that erasing the visible
proofs recovers exactly the original `family.terms` finset.

The import-facing theorem
`ordinaryTraceAlong_g8FamilyVisibleBoundary_eq_finitePrimeTerm_sum` then applies
the existing selected-Euler boundary trace theorem and reads the assembled
visible-place operator back to the original finite prime-power sum.  The proof
uses only the finite-map/attach identities and explicit per-term
`GlobalPrimePowerTraceBasisData`.

## Scope and status

This is a FORMAL arithmetic-side P1 consumer.  It establishes ownership and
exact finite trace bookkeeping; it does not identify the metric Schur boundary
column with this radial crossing assembly, prove a cutoff remainder limit, or
prove the detector-specific P2 inequality.  Therefore P2 and P3 remain open.

## Verification

Owning and audit targets were built in
`1408_g8_finite_prime_assembly.log`: the log contains the success footer for
3164 jobs, no `error:` or `sorryAx`, and the three audited declarations print
exactly `[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
