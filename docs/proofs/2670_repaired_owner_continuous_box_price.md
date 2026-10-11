# Record 2670 - repaired-owner continuous-box price

**Verdict: CONTINUOUS-BOX-PRICE-PASSES AT 2048 AND 8192 CELLS; PROOF OPEN.**

A cell bound (one upper bound valid across an entire small interval) can price
the finite-support integral without a trapezoid remainder. For each cell, this
probe takes the 2242 interval hull, bounds its complex modulus with MPFR
upward-rounded square/add/square-root operations, bounds the exponential
weight at the correct endpoint, and accumulates
`cell width * modulus upper * weight upper` with upward rounding. This is a
numerical design price; the evaluator and the resulting finite sum are not yet
imported into Lean.

The owner inputs are the 2338 coefficient-ball midpoints cast to binary64,
with hashes checked against the repaired treatment in 2665. The domain is the
corrected-profile support `[-6.553600000000003, 6.553600000000003]`, and the
weight parameter is `sigma = -0.5`.

Each family width is loaded as an exact binary64 operand and squared at 256-bit
MPFR precision. Its 53-bit significand squares to at most 106 bits, so the
radius stored in the interval evaluator is exactly `storedWidth^2`; all 30
family radii are configured this way. The integration partition endpoint is
rounded outward above the exact maximum support. This closes the numerical
radius mismatch in the earlier 2670 run; the exact operation and interval
soundness still need Lean proofs.

## Readback

```text
+-------+------------------+----------------------+----------------+
| cells | total upper      | ratio to knownError  | budget check   |
+-------+------------------+----------------------+----------------+
|   512 | 137951046.886319 | 1.8491718109         | above budget   |
|  2048 |  28212688.794263 | 0.3781784191         | below budget   |
|  8192 |   6705960.433245 | 0.0898903870         | below budget   |
+-------+------------------+----------------------+----------------+
```

The budget is `knownError2109 = 74601530.30234718`, read from the committed
2109 ledger and compared as an exact decimal rational. The 8192-cell total is
dominated by `corr_D2 = 6688178.977089`; the other channel uppers are
`base_M0 = 4.876877`, `base_D2 = 13892.045979`, and
`corr_M0 = 3884.533300`. The 2048-cell partition is already below budget, so
the numerical result supports continuing with this direct enclosure route.

This is much more conservative than the 2668 nodal sum (134146.400373), as
expected: each cell pays its whole interval hull. The price trend improves as
cells narrow, but it does not validate the method or close any theorem by
itself.

## Remaining proof gates

1. Prove once in Lean that the exact stored widths square to the evaluator's
   radius literals and that the 2242 interval operations enclose the stated
   continuous functions; then replay the finite cell bounds and their sum.
2. Prove that these four repaired-owner integrals bound the exact `chargeRest`
   term for the owner used by the live producer, including coefficient-ball
   membership and owner identity.
3. Close the separate signed infinite-xi tail and compose the result into the
   existing producer theorem.

Until those links are proved, `continuum_enclosure_proved`,
`actual_owner_identity_proved`, `infinite_xi_tail_closed`, `producer_go`, and
`rh_claim` remain false.

## Evidence

- `scripts/routea_repaired_owner_continuous_box_price_2670.py`
- `results/2670_repaired_owner_continuous_box_price.json`
- `scripts/routea_repaired_owner_pointbox_control_2669.py`
- `results/2669_repaired_owner_pointbox_control.json`
- `docs/proofs/2668_repaired_owner_fullgrid_replay.md`
- `docs/proofs/2252_routea_weighted_zero_item5_arithmetic_lean.md`
