# CC20 compact interval measure

The compact interval is now equipped with the explicit subtype measure

```text
cc20CompactMeasure = Measure.comap Subtype.val volume.
```

Lean proves

```text
cc20CompactMeasure univ = ENNReal.ofReal (3/2),
```

using the measurable subtype embedding and the exact real interval-volume
formula. The measure is registered as finite, so it satisfies the finiteness
assumption required by `ContinuousMap.toLp_denseRange`.

This fixes the measure domain for the next `L2` estimate. It does not itself
prove an `L2` operator bound, a Hilbert--Schmidt identity, the CC20 source
action, or RH.
