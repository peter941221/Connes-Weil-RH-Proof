# G8 P1 endpoint orientation bridge (2026-09-10)

The import-facing leaf `C1G8P1EndpointOrientation` proves the exact uncut
same-owner alignment

```text
  L† W_g J = -(sourceBandGramResponse owner lambda family)†,
```

where `L = finiteEulerMetricCoframe − J` is the physical G8 leakage coframe.
The proof composes three existing same-owner identities: the G8 leakage cross
is `finiteEulerTargetCommutatorResponse`, the latter is the left-ordered Gram
response, and the route-band orientation is the negative of that Gram order;
the source-band order is its adjoint. No owner, detector, finite family, or
source carrier is changed.

This is a formal orientation bridge only. It does not identify the ordinary
trace with the finite prime-power scalar, prove cutoff convergence, establish
the P2 aggregate inequality, or produce a P3 `qw` readback.

Acceptance: `/home/peter/rh/build-logs/1311_g8_p1_endpoint_orientation.log`,
3926 jobs, zero `error:`/`sorryAx`, and the paired audit has only
`[propext, Classical.choice, Quot.sound]`.
