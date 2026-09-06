# 1192 - Line B canonical-cutoff producer obstruction

Date: 2026-09-06.

Status: FORMAL conditional no-go for the canonical qIntegrand-prefix route.
P2 and RH remain open.

## Result

The theorem
`no_selectedOwner_canonicalQIntegrandPrefix_of_orbit_control_at_cutoff`
removes the auxiliary cutoff-equality premise from the earlier guard.  For a
canonical producer on the selected owner, the producer's own cutoff defines
the finite shell prefix.  If the selected square kills every source zero
outside the chosen functional-equation orbit in that prefix, then the
orbit-controlled prefix is at most `-xiMultiplicity rho`, while the
endpoint-corrected qIntegrand/Wirtinger identity makes the same prefix
nonnegative.  The two facts contradict positive multiplicity.

This is a genuine formal obstruction to the canonical-prefix producer under
the stated orbit-control hypothesis.  It is not a refutation of the whole
Bombieri line: a producer could still have to avoid this exact control shape,
or use a different signed semi-local owner.  No positivity conclusion or RH
claim is added.

## Evidence

The owning module and paired audit are
`ConnesWeilRH/Dev/C1P2SpectralHorizontalDefect.lean` and
`ConnesWeilRH/Dev/C1P2SpectralHorizontalDefectAudit.lean`.

Focused WSL build: `build-logs/lineB-cutoff-wrapper.log`, footer
`Build completed successfully (3666 jobs)`, zero `error:` and zero `sorryAx`.
The new declaration audits to exactly
`[propext, Classical.choice, Quot.sound]`.
