# Route A parameterized four-channel partition contract (record 3050)

The existing 2682 and 2683 channel theorems prove containment only on
`Icc 0 record2675CellRight`. The generic 2686 theorem already accepts a finite
partition, but no Route-A module currently supplies its four channel premises
for every partition index.

The next implementation must expose one indexed contract:

```text
endpoint : Nat -> Real
baseM0Rect, baseD2Rect, correctionM0Rect, correctionD2Rect : Nat -> ComplexRect
weightBound, baseM0Norm, baseD2Norm, correctionM0Norm, correctionD2Norm : Nat -> Real
charge : Nat -> Real
```

For every `k < n`, it must prove:

```text
endpoint k <= endpoint (k+1)
rect_k contains the corresponding live channel on Icc(endpoint k, endpoint (k+1))
cornerNorm(rect_k) <= norm_k
exp(sigma*x) <= weightBound k
width_k * weightBound k * norm_k <= charge_k
```

The four channel functions must be exactly:

```text
externalPhysical2344 record2678BaseCoefficient capturedModulations2584
second derivative of correctedPhysical with record2678BaseCoefficient
externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
second derivative of correctedPhysical with record2680CorrectionCoefficient
```

The first concrete bridge should parameterize the existing fixed interval
proofs instead of copying 10240 theorem bodies. Until this contract is
instantiated for all cells and its charge sum is connected to `chargeRest`, no
Producer GO or RH claim is licensed.
