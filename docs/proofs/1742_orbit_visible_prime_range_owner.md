# 1742 - Orbit visible-prime range owner

Date: 2026-09-20.

Status: FORMAL, supporting brick for the healthy-`CompactLog` B5 mainline.
This record does not prove semi-local positivity and does not claim RH.

## Result

The raw `OrbitG8Geometry` package already carried a strict real cutoff for
every visible prime-power index of the selected convolution square:

    q < exp (2 * (orbitIndex + 2)).

The new theorem
`visiblePrimeSet_subset_range_of_orbitG8Geometry` converts that cutoff into
the executable finite owner

    globalPrimeIndexSet g.convolutionSquare ⊆
      range (ceil (exp (2 * (orbitIndex + 2))) + 1).

The companion theorem
`finitePrimeSum_eq_sum_range_of_orbitG8Geometry` rewrites the same-owner
finite prime contribution over that range, with all non-visible terms proved
zero from the existing prime-power characterization.

The proof uses only `Nat.le_ceil`, an exact cast back to `Nat`, and the strict
successor range bound.  It introduces no sign premise, no stored conclusion,
and no axiom beyond the standard audit trio.

## Consumer

The theorem supplies the explicit finite index domain needed by the next
selected-detector sign brick: rewrite the same-owner finite prime sum over a
natural-number range fixed by the detector's own support/orbit index, then
prove the aggregate archimedean-plus-prime inequality on that owner.

This is ownership plumbing, not positivity.  The open mathematical target
remains the detector-specific semi-local gate.

## Verification

Owning module and paired audit:

    lake build ConnesWeilRH.Dev.C1G8R0OrbitGeometry \
      ConnesWeilRH.Dev.C1G8R0OrbitGeometryAudit

Accepted log: `build-logs/shortest_route_20260920_g8r0.log`.
The log has zero `error:` lines, the success footer, and the new theorem's
axioms are exactly `[propext, Classical.choice, Quot.sound]`.
