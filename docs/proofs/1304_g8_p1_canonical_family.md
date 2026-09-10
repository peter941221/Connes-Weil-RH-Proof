# G8 P1 canonical exact-support family

The import-facing leaf `C1G8P1CanonicalFamily` introduces
`g8CanonicalFamily owner := ofSelectedOwner owner`.  Its theorem
`g8CanonicalFamily_pow_mem_iff` identifies the powered terms with exactly the
selected owner's `IsPrimePow` atoms having nonzero `finitePrimeTerm`.  The
theorem `g8CanonicalFamily_visiblePrime_iff` then identifies a visible place
with a genuinely prime base and a nonzero power term; the `1 < p` proof stored
by `CCM24VisiblePrime` is not incorrectly treated as primality.  Finally,
`g8CanonicalFamily_visiblePrime_lt_globalIndexBound` carries the support-derived
finite cutoff of the same owner to the visible list.

The same leaf also proves
`ordinaryTraceAlong_g8CanonicalFamilyVisibleBoundary_eq_selectedSupport_sum`:
the selected-Euler boundary trace is exactly the sum over the selected
owner's canonical exact-support index set.

This is FORMAL same-owner P1 finite-support/readback evidence: owning build
`1430_g8_p1_canonical_family_trace.log` and paired audit
`1431_g8_p1_canonical_family_audit.log`, 3705 jobs, zero `error:`/`sorryAx`, and
only `[propext, Classical.choice, Quot.sound]` in the paired audit.  It binds
the arithmetic visible set and finite trace endpoint to the selected detector,
but it does not identify
the metric Schur boundary maps with radial crossings, prove a finite metric
trace equality, or supply the P2 remainder/sign producer.
