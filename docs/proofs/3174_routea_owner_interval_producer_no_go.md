# 3174: Route-A owner interval producer feasibility no-go

Status: `A-DEAD-CURRENT-PAYLOAD` on 2026-10-29.

This record answers one narrow question:

Can the existing numerical artifacts instantiate the actual same-owner
`RouteAOwnerNodeIntervalCertificate` contract and therefore feed the Route-A
physical-kernel gate?

The answer is no for the current artifacts. This is not a global no-go for
Route A or for every future selector.

## Target contract

The required producer has to preserve the selected owner, the visible prime
range, signed cancellation, and both frequency signs:

```text
for every rho with 1/2 < Re(rho)
        |
        +--> choose g and geometry : OrbitG8Geometry rho g
        |
        +--> lower[n] <= actual signed node[n] <= upper[n]
        |
        +--> archimedeanTerm + sum(upper[n]) <= 0
        |
        +--> same-owner physical-kernel gate
```

Here an interval enclosure means a proved lower and upper bound for the same
mathematical object. It is stronger than a high-precision sample: a sample
only evaluates selected points, while an enclosure proves that every allowed
value lies inside the interval.

The exact node is defined in
`ConnesWeilRH/Dev/C1RouteAOwnerPhysicalKernelCertificate3172.lean:15` as

```text
vonMangoldt(n) / sqrt(n)
  * Re(K_geometry(log n) + K_geometry(-log n))
```

The finite readback in
`ConnesWeilRH/Dev/C1P2OrbitPhysicalProfileReadback.lean:203` confirms that
the range is the geometry-owned `orbitVisiblePrimeRange geometry`, and that
both `+log n` and `-log n` are part of the signed node. The end-to-end
consumer at `...C1P2OrbitPhysicalProfileReadback.lean:338` additionally
requires such a certificate for every admissible off-line zero `rho`.

## Evidence audit

```text
+------+--------------------------------------+------------------------------+------------------+
| Rec. | Artifact                             | What it actually proves      | Producer status  |
+------+--------------------------------------+------------------------------+------------------+
| 2523 | safe certificate                     | fixed 2463 midpoint,        | not owner node   |
|      |                                      | sigma = +/-1/2; node sum    |                  |
|      |                                      | remains                       |                  |
| 2530 | signed node payload                 | diagnostic center/error      | no directed      |
|      |                                      | payload                       | enclosure        |
| 2535 | whole-cell enclosure               | external base coefficient    | not Lean; no     |
|      |                                      | box and derivative argument  | signed kernel    |
| 2539 | signed aggregate Lean audit        | analytic cell inequalities   | coefficient      |
|      |                                      | and source identity          | membership open  |
| 2038 | one-copy interval audit            | current finite-window no-go  | full-line tail   |
|      |                                      |                               | missing          |
+------+--------------------------------------+------------------------------+------------------+
```

The stored payloads make the boundary explicit:

- `results/2523_safe_certificate.json` has scope `fixed 2463 midpoint
  function, sigma +/-1/2; node sum remains`.
- `results/2530_signed_node_center_error_payload.json` is marked
  `CENTER_PLUS_SCALAR_ERROR_NODE_PAYLOAD_DIAGNOSTIC`.
- `results/2535_whole_cell_enclosure.json` is marked
  `EXTERNAL_WHOLE_CELL_ENCLOSURE_NOT_LEAN`; its scope is `base coefficient
  boxes only; analytic derivative/envelope argument external`, and it records
  `complete_signed_kernel_priced: false` and `producer_go: false`.
- `results/2539_signed_aggregate_validation.json` records
  `lean_numeric_certificate: false`, `exact_owner_transfer: false`, and
  `producer_go: false`; its scope leaves coefficient membership and numeric
  evaluations open.
- `results/2038_route_a_one_copy_interval_certificate_audit.json` marks the
  one-copy attempt `A-DEAD-CURRENT-CERTIFICATE`. Source transform, signed
  kernel, coefficient solve, finite-window quadrature, and the full-line tail
  are not all closed.

The source search also found no constructor or instance of
`RouteAOwnerNodeIntervalCertificate` or `OrbitPhysicalKernelNodeCertificate`
outside their definitions and conversion theorems. Therefore the current
repository contains the socket, but no data-bearing plug.

## First-principles failure mechanism

The mismatch has three independent causes:

1. The existing payloads are fixed-owner or fixed-midpoint computations. The
   consumer is uniform in `rho` and chooses a fresh `OrbitG8Geometry` owner.
   A fixed numerical owner cannot discharge that quantifier.

2. The existing cell bounds are bounds over physical support cells or strip
   norms. The target node is a signed arithmetic sum at `+log n` and
   `-log n`, weighted by `vonMangoldt(n) / sqrt(n)`. A support-cell bound does
   not automatically become a bound for this weighted node.

3. Replacing each signed node by a norm majorant would erase the cancellation
   that the live gate needs. No aggregate `<= 0` result for that replacement is
   present, and treating it as the target would change the mathematical
   producer rather than prove the existing one.

Consequently, filling 3173 with `nodeBound := actual node` would merely move
the missing inequality into `aggregate_upper`; filling it with a positive norm
bound would change the object and still leave the budget unproved.

## Decision

Stop the current 2037/2081 one-copy numerical payload as a producer source.
Do not add generated intervals to Lean until all of the following are available
for the same owner object:

```text
source-transform enclosure
        + signed physical-kernel enclosure
        + coefficient enclosure
        + finite-window quadrature enclosure
        + full-line/tail enclosure
        + exact orbitVisiblePrimeRange geometry
        ------------------------------------------------
        = lower[n], upper[n], aggregate_upper <= 0
```

The reusable Lean interfaces 3172 and 3173 remain valid. This record only
closes the current payload-to-producer attempt and prevents a sampled or
external interval from being promoted to `SourceRH`.

## Next producer target

The next useful artifact is a same-owner interval engine whose output is
parameterized by the actual `OrbitG8Geometry` and whose final export contains
the exact rational `lower[n]`, `upper[n]`, and aggregate budget. The first
successful checkpoint is not a negative floating-point reading; it is one
fully closed node family with both signs and an independently checked tail.

Until that checkpoint exists, additional model refinement or grid refinement
does not remove the blocking premise.

## Nonclaims

- This record does not prove or disprove RH.
- It does not prove that every future Route-A selector fails.
- It does not invalidate the Lean contracts in 3172 or 3173.
- It does not transfer any Route-B or row-B result to Route A.
