# 1647 — Detector renewal trace legality is closed; the sign is not

The existing source modules already establish the following formal facts for
the finite-Euler detector corner:

1. each displacement atom
   `rootCompletedDetectorSoninTranslationPair` is trace-class along the named
   global basis;
2. the complete finite-Euler corner is trace-class before any renewal
   expansion;
3. its trace has the ordered readback

```text
sum_basis sum_renewal weight(renewal) * displacementRootPairing.
```

The relevant declarations are
`rootCompletedDetectorSoninTranslationPair_isTraceClassAlong`,
`sourceRootCompletedFiniteEulerCorner_isTraceClassAlong`, and
`sourceRootCompletedFiniteEulerTrace_eq_iterated_rootPairing_tsum`.

This does not prove the required `qw >= 0`. The readback is explicitly a
signed scalar series; no termwise positivity or renewal-sum sign theorem is
present. Therefore the next producer target is the positivity of the complete
same-owner aggregate (including its signed compact-kernel remainder), followed
by the existing G8 aggregate-to-Weil consumer. Trace legality must not be
reopened as the main obstacle.

No RH conclusion is claimed.
