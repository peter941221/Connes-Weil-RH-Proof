Record 2651: cell5440 discharge — sigma=+1/2 conditional inventory cleared GREEN
Date: 2026-10-10

Result

Positive: `ConnesWeilRH/Dev/C1RouteACell5440Discharge2651.lean` built
green FIRST TRY in one build (`ℹ [3917/3917] Built ... (1.2s)` +
`Build completed successfully (3917 jobs)`; 0 error, 0 `uses sorry`,
0 module warning; both new theorems depend only on
`[propext, Classical.choice, Quot.sound]`).  The full graph replayed
from the freshly repaired 2650 mirror state; only the new module
compiled.

The 2650 discharge pattern applied verbatim to the second — and
last — sigma = +1/2 conditional entry of the lane-A audit:

1. Region form — `cell5440_boxDischarge2651`: the 2546 certificate
   (integral ≤ 379207837/500000000000 = 7.58415674e-4) extends from
   the coefficient ball to the whole record-2338 base-coefficient
   region.
2. Unconditional form — `cell5440_center_discharge2651`: zero
   premises; the bound holds outright at the exact-rational center
   owner.

Inventory effect

    cell        sigma   before 2650/2651            after
    2700        +1/2    conditional (2551 ball)     region + unconditional (2650)
    5440        +1/2    conditional (2546 ball)     region + unconditional (2651)
    2700        -1/2    correction-pair chains      open (unknown #2: pipeline rerun)

The sigma = +1/2 side of the audit inventory now carries ZERO
coefficient-ball conditionals.  The two discharged cells — margins
1.14e-10 and 7.58e-4 — both survived discharge untouched; the
coefficient-ball premise class is confirmed to be bookkeeping, not
mathematics, everywhere it has been tested.

What this does not claim

No grid claim beyond the two discharged cells; the sigma = -1/2
boundary chain (unknown #2) and exact-owner transfer (unknown #3)
remain open.  Producer GO, SourceRH, RH remain open.

Next obligations

1. Unknown #2: rerun the 2547-2551 boundary pipeline at sigma = -1/2
   (generators + payloads + Lean layer), then discharge by the same
   pattern.
2. Unknown #3: exact-owner transfer composition — assemble the
   2452/2453-54/2455-59 per-seam imports into a live-tuple box-
   membership assertion so the region forms reach the live consumer.
3. Parallel 2649 lane: 190-panel partition over column 3, then the
   (0,3) entry containment against the committed 2597 rectangle.
