# Record 1155 — P2 narrow reference-window certificate

Date: 2026-09-06

## Result

`C1P2NarrowWindowCertificate.lean` transfers the existing strict sign of the
explicit `narrowArchRoot` into the P2 gate language.  Its square has open
prime-free support, so

```text
ICgate(narrowArchRoot□)
  = archimedeanTerm(narrowArchRoot□) < 0.
```

Consequently there is an exact positive margin
`μ = -ICgate(narrowArchRoot□)` with
`ICgate(narrowArchRoot□) ≤ -μ`.  A producer using the P2 one-window witness
may therefore take this fixed narrow root as the reference window and only
owe the detector/window defect budget and its margin comparison.

The owning and audit modules build successfully in 3674 jobs.  The audited
declarations use only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This is a FORMAL reference-window certificate, not a comparison theorem for
the orbit detector.  It does not establish the detector's defect bound,
profile sign, or semi-local positivity.  P2/C3 remains OPEN and RH is not
claimed.
