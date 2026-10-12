# Record 2674 - binary64 endpoint certificate bridge

Verdict: BINARY64-DECODE-CERTIFICATE-INTERFACE-PASS; evaluator replay remains open.

The 2670 evaluator returns binary64 endpoints after its MPFR calculations. A
Lean consumer needs to interpret each endpoint as its exact rational value and
check that it encloses the exact value being rounded. This record adds
`ConnesWeilRH/Dev/C1RouteABinary64Bridge2674.lean`:

- `binary64Value2674` decodes a 64-bit IEEE-754 pattern to an exact rational,
  handling sign, subnormal values, and normal exponents;
- lower and upper certificate structures carry the bit pattern, exact input
  rational, and a checkable enclosure inequality, while requiring a 64-bit
  finite encoding;
- `mem_binary64Interval2674` turns certified directed lower and upper
  endpoints into membership in `RealInterval2429`.

The audit proves exact decodings for `1.0`, `-0.5`, and the least positive
subnormal, checks a paired endpoint certificate, and audits the three soundness
theorems. Linux Mathlib v4.30 compilation passes; all three declarations use
only `[propext, Classical.choice, Quot.sound]`.

The runtime control in `scripts/routea_binary64_endpoint_control_2674.py`
uses 256-bit MPFR to form the exact dyadic value `1 + 2^-200`, then converts
down and up. The observed bit patterns are `0x3ff0000000000000` and
`0x3ff0000000000001`; exact rational comparisons confirm containment. The
readback is in `results/2674_binary64_endpoint_control.json`.

This control validates one concrete conversion path, not MPFR's implementation
or every evaluator operation. The Lean certificate interface checks any
exported exact rational and endpoint pair once supplied; a complete 2670 proof
still needs certificates for the actual cells, soundness of the evaluator's
arithmetic and transcendental bounds, the finite sum, live-owner `chargeRest`,
and the signed infinite-xi tail. Producer GO and RH remain open.
