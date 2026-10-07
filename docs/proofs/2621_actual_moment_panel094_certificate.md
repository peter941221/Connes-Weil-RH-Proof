Record 2621: first actual degree-32 moment-panel certificate
Date: 2026-10-07

Result

The result is positive: panel 094's complete actual integral error is now
Lean-certified, not merely its scalar exponentials. The interval is the same
normalized [1/25,1/20] = [0.04,0.05] from the committed 180-panel partition.
No owner, coefficient convention, interval target, or physical multiplier
has been changed. The other 179 panels and full (0,0) containment remain
open; producer GO and RH remain false.

Let r be storedWidth(0)^2, the actual physical support radius, and f(u) be
realNormalizedMomentIntegrand2618(r,capturedNodes2584(0).re,u). The final
theorem states that r times the integral of f over [1/25,1/20] differs from
the exact rational momentPanelIntegralCenter2621 by at most 1e-82.
The finer exact charge is momentPanelIntegralCharge2621, displayed as
5.3754952698072625e-83. The center is displayed as
2.5126840456170858e-15; its full rational value, not this decimal display,
is used in the theorem and validation artifact.

The completion boundary is explicit:

```text
+--------------------------------------+------------------------------+
| Obligation                           | Current evidence             |
+--------------------------------------+------------------------------+
| Actual owner and exponent scalars    | 2620 certified prerequisites |
| Degree-32 polynomial derivative      | Generic proof + exact replay |
| Residual identity and upper bound    | Exact replay + generic proof |
| Polynomial integral                  | Certified primitive          |
| Actual panel [0.04,0.05] integral    | Error <= 1e-82, Lean-proved   |
+--------------------------------------+------------------------------+
| All 180 panels and assembly          | Not certified                |
| Full actual (0,0) rectangle          | Not certified                |
| Matrix, coefficients, signed budget  | Not completed                |
+--------------------------------------+------------------------------+
```

Why this closes the panel

A polynomial is a finite sum of powers: for example, coefficients [1,2,3]
represent 1 + 2*t + 3*t^2. Record 2621 stores exact rational coefficients,
not floating-point approximations. The generic helper proves that its list
addition, scaling, multiplication, derivative, and real evaluation have
their usual mathematical meanings.

For this actual owner, beta is capturedNodes(0).re*r, c=9/200 is the panel
center, h=1/200 is its half-width, and t is displacement from its center.
The exact exponent is H(t) = -30/(1-(c+t)^2) + beta*(c+t).
S(t) is the degree-32 rational polynomial with S(0)=1. It approximates
exp(H(t))/exp(H(0)), so the exponential amplitude remains separate.

D(t) = (1-(c+t)^2)^2 removes the derivative's denominator, and
N(t) = beta*D(t) - 60*(c+t). The residual Q(t) = D(t)*S'(t) - N(t)*S(t)
measures how far S deviates from that exact differential equation. This is
like checking how closely a proposed path obeys its equation of motion,
instead of differentiating the true path dozens of times.

The generated table is not trusted. Lean replays its rational arithmetic
and proves that Q's coefficients 0..31 are exactly zero, with only the five
slots 32..36 left. A generic Horner absolute bound proves abs(Q(t)) <= M
on abs(t)<=h, where M is the exact momentPanelResidualUpper2621, displayed
as 4.030925e-66. Horner evaluation is nested evaluation of the same power
sum; it also gives a compact computational representation for replay.

The existing 2619 stability theorem converts that residual bound into an
integral error. Its denominator lower bound is d=(1-(abs(c)+h)^2)^2; V is
the proved exponent-variation bound. The normalized error charge is
exp(H(0))*exp(2V)*(M/d)*(2*h^2). Record 2620 supplies certified upper bounds
on both exponentials. This is a proof chain, not a comparison of two
numerical answers.

A primitive is a function whose derivative is the polynomial. Record 2621
also generates an exact rational primitive and replays its derivative
against S. The fundamental theorem of calculus then evaluates the
polynomial integral by subtracting its two endpoint values.

Finally, the center uses the certified exponential's rational center A,
not the exact exp(H(0)). The amplitude radius eA is therefore charged once
more against abs(I), where I is the exact polynomial integral:

  center = r*A*I
  charge = r*(analytic_charge + eA*abs(I))

Both equalities are exact rational replay theorems. The final consumer
proves the normalized integrand agrees with exp(H) throughout the panel,
retains r, and translates the local interval [-h,h] to [0.04,0.05].

Validation and limits

All 26 audited leaves have exactly [propext, Classical.choice, Quot.sound].
Four modules rebuild successfully in the final fingerprinted control:
6.34 seconds total compiler wall time, peak RSS 4,131,976 KiB (about
3.94 GiB). This is a warm-cache local build, not an upstream rebuild.

Fourteen new tests pass. They compare the Fraction recurrence with the
independent older FLINT recurrence, reconstruct derivatives and symmetric
power integrals, check signed sample residuals, and reject perturbed
coefficients and primitives. A 512-bit Arb degree-48 model enclosure lies
inside the new panel radius. That model is a test control, not a Lean proof
input. Generated-source and payload-scope drift are also rejected.
All 2618..2621 regression suites pass: 45 tests total.

The first selftest draft wrongly expected one extra trailing zero in list
multiplication. The actual recurrence and independent engine already agreed;
the assertion and corresponding unused tail-zero statement were corrected
to the representation's actual length, then regenerated and fully validated.
No analytic bound, target interval, or charge was loosened.

The validator checks current generated sources/payload, owner capture and
witness fingerprints, and the certified 2620 source/object prerequisites.
It checks all newly compiled and inherited 2620 source/object hashes again
at the end. The generated payload remains lean_verified=false; the separate
validation artifact certifies only this panel and polynomial table.

The payload generator explicitly writes LF newlines on both Windows and
Linux. A payload selftest rejects CRLF, and pre-publication checks require
staged bytes to equal working-file bytes, so Git normalization cannot
silently invalidate the published fingerprints. Both the scalar and panel
validation artifacts were refreshed after the newline fix.

Primary evidence:

  ConnesWeilRH/Dev/C1RouteARationalPolynomial2621.lean
  ConnesWeilRH/Dev/C1RouteAMomentPanelTable2621Panel094.lean
  ConnesWeilRH/Dev/C1RouteAMomentActualPanel2621Panel094.lean
  ConnesWeilRH/Dev/C1RouteAMomentPanelAudit2621.lean
  scripts/generate_moment_panel_certificate_2621.py
  scripts/validate_moment_panel_certificate_2621.py
  scripts/moment_panel_certificate_selftest_2621.py
  results/2621_moment_panel_payload.json
  results/2621_moment_panel_validation.json
  results/2621_moment_regression_validation.json

Reproduction interface

Run scripts/validate_moment_panel_certificate_2621.py in Linux with the
explicit complete native LEAN_PATH. --workspace selects the complete
project library; --logs selects the resource/audit log directory; --lean
selects the pinned compiler; --test-python selects a python-flint-enabled
interpreter. The validator requires current certified 2620 objects and emits
ACTUAL_PANEL094_INTEGRAL_LEAN_CERTIFIED only after tests, four successful
builds, exact axiom audits, and end-of-run freshness checks.

Next steps

1. Parameterize the same actual-panel consumer and generate the remaining
   179 panels. Each needs its own polynomial, residual, primitive, and
   exponent certificates. Completion means each actual interval has a
   checked error, including amplitude-center replacement and physical r.

2. Assemble the 180 adjacent intervals and both certified edges into the
   actual full integral. This establishes that no region is missing or
   double-counted. Completion means the unchanged original real bounds
   contain the actual (0,0) integral; join with 2618's exact imaginary zero.

3. Certify a non-diagonal entry before matrix-wide expansion. Its phase does
   not automatically cancel, so the complex-valued version must be checked.
   Completion means both coordinates are enclosed for the same actual owner.
   Matrix/coefficients and the selected detector's signed budget remain
   later obligations, not consequences of this first panel.
