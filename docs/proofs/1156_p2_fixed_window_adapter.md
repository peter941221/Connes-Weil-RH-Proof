# Record 1156 — P2 fixed-window canonical adapter

Date: 2026-09-06

## Result

`C1P2NarrowWindowCertificate.lean` exports the source support of the fixed
`narrowArchRoot` and introduces `P2NarrowReferenceCanonicalWitness`.  Its
`toCanonical` map instantiates the existing canonical one-window contract
with the same root owner, its exact negative `ICgate` margin, and the root
support interval.  The resulting
`orbitGate_of_p2NarrowReferenceCanonicalWitness` feeds the unchanged healthy
`CompactLog` B5 consumer.

The new payload leaves only three producer inputs: detector support, the
same-owner defect budget, and the scalar margin comparison.  No sign is stored
in the payload and no detector/window comparison is inferred.

The owning and audit modules build successfully in 3674 jobs.  Audited
declarations use only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This is FORMAL interface compression.  It does not prove the defect budget,
the bilateral profile sign, semi-local positivity, or RH.  P2/C3 remains
OPEN.
