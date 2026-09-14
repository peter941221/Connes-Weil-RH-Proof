# 1431 — R3 doubled-shift projection transport

Date: 2026-09-14

## Result

The R3 doubled-shift candidate now has a formal projection transport, not
only the previously landed closed-subspace transport.  For
`b = log lambda`, the new operator is
`doubledShiftSoninProjection b = U_b R_b U_(-b)`, where `R_b` is the
orthogonal projection onto the doubled-shift Sonin closed subspace.  The
formal results prove:

1. the conjugated operator is a star projection;
2. its range is the source Sonin projection's range;
3. equality with the canonical source Sonin projection.

The construction uses only the committed unitary translation, the T1
closed-subspace identity, and the orthogonal-projection API.  It introduces
no trace assertion, sign conclusion, `SourceRH`, or external dictionary.

## Formal artifacts

- `ConnesWeilRH/Dev/C1G8R3DoubledShiftSoninTransport.lean`
  - `doubledShiftSoninProjection`
  - `doubledShiftSoninProjection_isStarProjection`
  - `doubledShiftSoninProjection_range_eq_source`
  - `doubledShiftSoninProjection_map_eq_source`
- paired audit module:
  `ConnesWeilRH/Dev/C1G8R3DoubledShiftSoninTransportAudit.lean`

## Acceptance evidence

Build log:
`build-logs/1431_doubled_projection_batch_try6.log` in the standard WSL
build mirror.

The focused build of both the implementation and audit targets reports:

```text
Build completed successfully (3176 jobs).
^error: count = 0
sorryAx count = 0
8 audited Quot.sound] occurrences
```

The eight audited declarations all print exactly
`[propext, Classical.choice, Quot.sound]`; four are the new projection
declarations and four are the previously landed T1 declarations.

## Scope judgment

This is a genuine formal reduction of R3, but it is not R3 completion.  The
detector-weighted trace-class estimate, global basis witness, signed limit,
G8 same-owner readback, and the final RH composition remain open.
