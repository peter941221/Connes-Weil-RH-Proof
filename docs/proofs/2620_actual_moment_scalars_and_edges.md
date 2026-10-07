Record 2620: actual-owner exponential certificates and both edge integrals
Date: 2026-10-07

Result

The result is positive but local: three concrete exponentials and the actual
(0,0) moment's two edge integrals are now Lean-certified. The interior
polynomial tables, a complete panel integral, and actual matrix-entry
containment remain unproved. Producer GO and RH remain false.

What was certified

The owner is the captured (0,0) matrix entry, not a substitute function.
Here r is its physical support radius, equal to storedWidth(0)^2. beta is
capturedNodes(0).re times r. The normalized coordinate u represents physical
position r*u, so every final integral charge must retain the multiplier r.

The selected interior panel is panel 094 of the existing 180-panel partition:
center c = 9/200, half-width h = 1/200, hence u ranges from 0.04 to 0.05.
H0 = -30/(1-c^2) + beta*c is the exponent at its center. V is the existing
2619 upper bound on the exponent's change over this panel. The edge cut is
9/10, so the two excluded slices are [-1,-0.9] and [0.9,1].

```text
+------------------------+-------------------+--------------------------+
| Certified object       | Error/charge      | Scope                    |
+------------------------+-------------------+--------------------------+
| exp(H0)                | radius <= 1e-80   | panel 094 amplitude      |
| exp(2V)                | radius <= 1e-70   | panel 094 growth factor  |
| exp(-30/(1-cut^2)      | radius <= 1e-90   | actual edge envelope     |
|     + abs(beta))       |                   |                          |
| r times both edge      | abs <= 2e-68      | actual integral theorem  |
| integrals together     |                   |                          |
+------------------------+-------------------+--------------------------+
```

Why the exponential engine changed

A certificate is a center together with a proved error radius: for example,
center 2 and radius 0.01 assert that the true number lies in [1.99,2.01].
An external high-precision answer alone does not establish that assertion in
Lean's proof checker. Record 2620 supplies both the algorithm's error proof
and exact replay of its concrete inputs.

Scaling and squaring first computes exp(argument/2^20), then squares twenty
times to recover exp(argument). Its Taylor polynomial keeps terms 0 through
19. The truncation proof retains the small argument's twentieth power:
abs(argument/2^20) <= 1/1000 implies truncation <= 1e-78. Reusing the older
coarse truncation allowance would not support this entry's 1e-64 target.

Coordinate rounding is directed downward at 320 bits; error radii are
directed upward at 400 bits. Directed rounding means deliberately rounding
on the safe side rather than treating a nearest-rounded value as exact.
If a state has center a and radius e, squaring propagates its uncertainty
through e*(2*abs(a)+e), then adds the proved coordinate-rounding charge.
Horner evaluation is nested polynomial evaluation, reducing repeated powers;
its concrete replay uses the same descending divisors 19 through 1 as Lean.

Evidence and validation

The owner equalities are Lean theorems against capturedNodes2584 and
storedWidth, not merely matching JSON hashes. All three replay equalities
use decide +kernel. The audit lists 22 leaves, each with exactly
[propext, Classical.choice, Quot.sound]; no new axiom or placeholder is used.

The validator rebuilds seven modules, requires successful process and
resource-runner exits, and records source/object SHA256 fingerprints.
SHA256 is a content fingerprint: changing a file changes its fingerprint,
so an old compiled proof cannot silently stand in for changed source.
Generated source and scalar payload are reconstructed exactly. Capture,
2351 witness, generator, validator, and selftest fingerprints are checked
or recorded. The generator's lean_verified remains false; only the separate
successful validation artifact asserts the narrower certified results.

Final warm-cache compiler wall time totals 9.63 seconds, with peak RSS
4,026,768 KiB (about 3.84 GiB). These are seven local module builds, not a
fresh upstream rebuild; earlier dependency bootstrap time is excluded.

Thirteen new tests pass. Independent 512-bit Arb balls check every one of
the 21 states for all three actual exponentials, not only their endpoints.
Other controls cover negative directed rounding, the tiny-argument boundary,
Horner order, nonnegative radii, rejected center perturbation, owner geometry,
and rejected generated-source, capture-fingerprint, and payload drift.
Arb is an independent interval-arithmetic test engine, not an input axiom
to the Lean proof. The 2618/2619/2620 regression bundle passes all 31 tests.

Primary artifacts:

  ConnesWeilRH/Dev/C1RouteACompactExpSharp3202620.lean
  ConnesWeilRH/Dev/C1RouteAMomentActualEdge2620.lean
  ConnesWeilRH/Dev/C1RouteAMomentScalarAudit2620.lean
  scripts/validate_moment_scalar_certificate_2620.py
  scripts/moment_scalar_certificate_selftest_2620.py
  results/2620_moment_scalar_payload.json
  results/2620_moment_scalar_validation.json
  results/2620_moment_regression_validation.json

Reproduction interface

Run scripts/validate_moment_scalar_certificate_2620.py in Linux with the
explicit complete native LEAN_PATH required by the project environment.
Its --workspace selects the existing complete project library; --logs
selects the resource/audit log directory; --lean selects the pinned v4.30.0
compiler; --test-python selects a Python interpreter with python-flint.
Successful execution emits ACTUAL_SCALARS_AND_BOTH_EDGES_LEAN_VERIFIED and
writes the validation artifact. Existing upstream objects are reused.

Generated JSON payloads explicitly use LF newlines. This preserves the raw
content fingerprints when Git normalizes line endings. Pre-publication
checks compare staged bytes with working-file bytes, and the selftest
rejects CRLF payloads. The final validation was refreshed after this fix.

Next steps

1. Certify panel 094's degree-32 rational polynomial. Its residual is the
   discrepancy between the polynomial and the exact differential equation:
   Q = D*S' - N*S. Prove the derivative identity, zero coefficients 0..31,
   bounds on the five remaining coefficients, and the exact polynomial
   integral. Completion means a proved actual panel error using these
   scalar certificates, not another external price.

2. Extend to the same 180-panel partition and assemble the actual real
   integral with the certified two-edge charge. Combine with 2618's exact
   imaginary zero. Completion means the unchanged original rectangle
   contains the actual (0,0) entry; no interval widening is permitted.

3. Validate a non-diagonal entry before matrix-wide generation. Unlike the
   diagonal entry, its phase does not automatically cancel. Completion
   means both real and imaginary coordinate certificates for the actual
   owner, establishing that the method generalizes before scaling to 900
   entries. Coefficient containment and the selected detector's signed
   positivity budget remain subsequent obligations.
