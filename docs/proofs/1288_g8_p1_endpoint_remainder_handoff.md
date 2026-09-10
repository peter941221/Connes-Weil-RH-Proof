# G8 P1 endpoint remainder handoff (2026-09-10)

The import-facing leaf `C1G8P1EndpointRemainder` combines the endpoint trace
orientation with the existing same-owner source-band decomposition. For every
admissible boundary pair and named source basis it proves

```text
Tr(L† W_g J)
  = −star(Tr(sourceActualBandFiniteEulerSoninResponse)
           − Tr(sourceActualBandFiniteEulerRemainderResponse)).
```

All support, basis, finite-family, and source-owner hypotheses are explicit.
The remainder remains a genuine named operator; no vanishing or estimate is
assumed. This fixes the exact scalar handoff needed before a finite
prime-power comparison and endpoint limit can be attempted.

Acceptance: `/home/peter/rh/build-logs/1317_g8_p1_endpoint_remainder.log`,
3927 jobs, zero `error:`/`sorryAx`, standard audit axioms only.
