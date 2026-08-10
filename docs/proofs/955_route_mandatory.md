# 955 - Are Wall-A 1.4 and Wall-B both mandatory for RH? (route verdict)

Date: 2026-08-10.  Status: route analysis (not a proof).  RH NOT claimed.

## Short answer

No, they are not both mandatory for every target:

- Wall-A 1.4 (the SCAL scalar identity) is effectively REQUIRED for the
  explicit-formula bridge that connects the arch/von-Mangoldt analytic side to the
  finite-prime side - the step that turns a finite-band/operator estimate into a
  statement about the non-trivial zeros.  It cannot be skipped.

- Wall-B (the infinite-carrier Gate identity (I-P)F = -(I-P)D) is NOT needed for
  the already-closed finite-band Route-A Gate.  The 2026-08-10 route decision
  (docs/928) deliberately made the finite/decaying-band carrier the canonical
  constructible deliverable and left the infinite carrier as a separate open
  analytic bottom.  So the finite-band target closes WITHOUT Wall-B.

- But a FULL / unconditional RH claim (whole strip, whole line) still needs either
  (a) moving the finite-band closure to the full carrier, which is essentially
  the infinite-carrier question, or (b) an RH-equivalent criterion.  For that goal
  Wall-B is in scope, not optional.

## Per-target necessity table

| downstream target          | Wall-A 1.4 needed | Wall-B needed |
|----------------------------|-------------------|---------------|
| finite-band Route-A gate   | no (already closed) | no            |
| global SCAL / psi sign     | yes                | indirect      |
| full / unconditional RH    | yes                | yes (or lift) |

## What remains regardless

The C1-RH criterion (CC2000PropositionC1SourceCriterionRoot, RH-equivalent) is an
independent hard step that no amount of the above two removes.  It is the actual
RH-equivalence discharge.

So: 1 must be done (it is the bridge); 2 is optional for the canonical finite
target but becomes necessary for a full RH lifting.  The recommendation stands:
attack Wall-A 1.4 first (target already pinned as a single scalar, docs/952-954).
