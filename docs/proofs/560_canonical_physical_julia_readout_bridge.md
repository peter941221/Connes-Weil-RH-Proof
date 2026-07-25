# Proof 560: canonical physical/Julia readout bridge

## Result

Proof 559's arbitrary Douglas factor is strengthened at the operator level.
For continuous linear maps `A` and `B` with the exact all-vector identity

```text
||A x|| = ||B x||,
```

the range-supported construction

```text
F = extension on closure(range B) * orthogonal projection onto closure(range B)
```

proves all three facts:

```text
||F|| <= 1
F B = A
F† F B = B.
```

The last equation is the point that an arbitrary Douglas witness does not
expose. It follows because the extension is an isometry on the dense range of
`B`, hence on its closure, and the domain projection kills the orthogonal
complement.

## Actual finite-S bridge

For the real CCM24 carriers, let `L` be the adjacent Julia `leftCoDefect`,
`A` the packed ambient-plus-moving-boundary analysis, and `F` the canonical
factor above. The new source module proves the exact same-bound conversions:

```text
raw = L * R
  ->  (R† * F†) * A = raw†,

D * A = raw†
  ->  raw = L * (D * F)†.
```

No channelwise estimate is introduced, no operator order is commuted, and the
readout/factor norm remains bounded by the original `bound`. The uniform
family theorem transports this conversion over every visible-prime/suffix
pair.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSDouglasFactor.lean
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaCanonicalAnalysisBridge.lean
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaCanonicalAnalysisBridgeAudit.lean
```

The new result is an exact carrier/orientation bridge. It does not construct
the missing uniform raw co-defect factor, prove the non-polar gap estimate,
close Gate 3U, prove the finite-S sign, supply Burnol's identity, or prove
`_root_.RiemannHypothesis`.
