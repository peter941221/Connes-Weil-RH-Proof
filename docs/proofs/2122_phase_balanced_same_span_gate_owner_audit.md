# 2122 — Phase-balanced same-span gate owner audit

Date: 2026-09-28.

Status: SCOPED NO-GO for gate reuse; phase-balanced route remains OPEN.
No producer theorem and no RH conclusion are claimed.

## Question

Can the closed gate theorem from map 091 be reused after the four-point
spectral transport in maps 094 and 103?

No. The obstruction is an exact object mismatch, not a numerical failure:

```text
091 gate object:
    spanObj ![narrowArchRoot, g] ![1, -ICgate(narrowArchRoot * g) / ICgate(g^2)]

094/103 spectral object:
    h(lambda) = annihilatorDetectorSpanVector
                 (fullFunctionalEquationOrbitAnnihilator g rho) g lambda
```

These are different `CompactLogTest` values. A gate theorem for the first
object does not provide `orbitWindowSemiLocalGate h(lambda)` for the second.

## Source evidence

1. `ConnesWeilRH/Dev/C1FourPointSpectralPrefixTransport.lean:44` defines
   `fullFunctionalEquationOrbitAnnihilator`, and `:330` proves only the
   finite-prefix spectral inequality for its transported span. The file header
   explicitly says that it does not prove the detector gate sign or the
   high-shell tail estimate.

2. `ConnesWeilRH/Dev/C1OrbitWindowSemiLocalGate.lean:57` defines the gate on
   the exact argument `g`; its bridge at `:63` consumes a gate for that same
   object.

3. `ConnesWeilRH/Dev/C1PinnedOrbitExit.lean:133` proves the existing pinned
   gate only for `spanObj ![narrowArchRoot, g]` with its selected coefficient.
   It does not mention `fullFunctionalEquationOrbitAnnihilator` or `h(lambda)`.

4. Map 094 and map 103 record that the high-shell tail and the same-span gate
   are independent open obligations, and that the 091 gate applies to a
   different test.

## Decision

```text
CLOSED:
    Reusing the 091 gate as the gate for the 094/103 transported span.

OPEN:
    Prove the gate directly for h(lambda), using its own support and visible
    prime-power domain, and intersect the admissible lambda region with the
    same-index high-shell tail budget.
```

The exact remaining gate interface is the span parabola formalized in record
1917:

```text
G(lambda) = D - lambda * B' + lambda^2 * C
```

The next quantitative target is an owner-matched result for the same `rho`,
`g`, support, visible-prime set, and `lambda`:

```text
tail(h(lambda), n) < xiMultiplicity(rho) * lambda^2
and
G(lambda) <= 0
```

The pair must hold for one common convolution index `n`; proving either half
in isolation does not close the contradiction.

## Reopen condition

This scoped no-go may be reopened only by changing a named hypothesis or
interface, for example:

- prove a gate theorem directly on `h(lambda)`;
- prove an invariant identifying `h(lambda)` with the 091 span, not merely
  support or triple-vanishing preservation; or
- replace the gate with a genuinely same-owner nonnegative functional whose
  input is `h(lambda)`.

No further work should try to transfer the 091 gate by support, triple
vanishing, or shared detector ownership alone.
