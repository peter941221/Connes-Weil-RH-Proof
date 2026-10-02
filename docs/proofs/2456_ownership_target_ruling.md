# 2456 - Ownership target ruling: the strip import binds the 2338 exact interpolation family, not the 2275 capture vectors

Date: 2026-10-02.

Verdict in one line: the coefficient vectors that any Lean-side strip
discharge (the 2343 endpoint hypotheses) and the downstream
FrozenStripHypothesis consumer may bind to are the 2338 exact
interpolation-solution balls - the 2275 capture vectors are excluded
from the production path by three committed records, and the
2452-2454 point-import lane stands as auxiliary import-mechanism
validation.

## The ruling is forced by committed records, not new policy

- 2337 (CAPTURED-MARKED-SIGN-CERTIFIED-ONLY): all eight mandatory
  source target values are excluded by their enclosures for the fixed
  captured coefficients - the raw moment at 1/2 has real part
  ~1.2708730094e-9 and imaginary part ~5.8737193146e-9, "nonzero
  residuals, not uncertainty radii". Verbatim: "The fixed captured
  coefficients therefore cannot be used as an exact finite-node
  realization.  A tolerance-only interpolation test would miss this
  failure."
- 2338 (EXACT-FINITE-NODE-REPAIR-ENCLOSED-ONLY): in the same 30-family
  basis, the analytic interpolation system A b = 1, A c = y is
  enclosed at 320 bits with a certified invertibility argument
  (eta = ||I - X A|| < 1/2, geometric-series invertibility), so the
  exact solution pair exists uniquely and its coefficient balls are
  exported.  "The live owner is not replaced" - the repair is a priced
  ideal candidate, and the owner's defining property is precisely the
  interpolation condition.
- 2351 (witness record): Lean already proves the actual CompactLog
  Laplace values equal A x coefficients, and that exact coefficients
  exist and are unique CONDITIONAL on the actual determinant being a
  unit; the numeric enclosure/invertibility import is the registered
  open item.

Consequences:

1. Any 2343 discharge constants must bound the strip integrals for the
   BALL family of the 2338 solution (every function with coefficients
   in the exported balls).  2342's four endpoint constants were
   computed on exactly those balls, so the external numerics are
   already aimed at the admissible target.
2. The 2452-2454 imports bind the 2275 capture binary64 vectors, which
   2337 excludes as an exact realization.  They remain valid as
   mechanism validation (the 2433/2437/2436 door, the 2453 bridge, the
   2454 sum-chain law), and their artifacts stay pinned; no production
   strip discharge may cite them as owner data.
3. Two import prerequisites follow, in dependency order:
   (a) discharge path: import the 2338 coefficient balls and the strip
   machinery (2455's W-A/W-B/W-C) so Lean can state and prove
   stripNorm bounds for the ball family;
   (b) instantiation path: import the certified invertibility so the
   owner instance exists in Lean (2351's open item).  The consumer
   needs both; (a) unblocks first.

## Scope

A routing note binding the import target.  No producer, no Lean
module, no strip norm discharged, no GO, no RH claim.

Evidence:

- `docs/proofs/2337_marked_sign_and_target_exclusion.md` (exclusion result)
- `docs/proofs/2338_exact_interpolation_repair.md` (exact family)
- `docs/proofs/2351_analytic_moment_witness.md` (Lean conditional form)
- `results/2342_direct_ideal_strip.json` (ball-family constants)
- `ConnesWeilRH/Dev/C1RouteAExternalOwnerIdentity.lean` (consumer face)
