# 097 Fixed-Detector Consumer Probe Pass

Date: 2026-07-12

## Lean evidence

`ConnesWeilRH/Dev/FixedDetectorConsumerProbe.lean` imports only
`CCM25Concrete.FinitePrimeExact` and defines a local
`FixedDetectorWeilData W f lambda` with:

```text
square
square_eq
ExactSupportAtLambda W f f lambda
qwDefinition
qwLambdaFormula
poleNormalization
```

The probe compiles and proves three fixed-test consequences:

```text
QW reads the same convolution square
QW_lambda reads the same square and local prime sum
ExactSupportAtLambda yields local prime visibility
```

It does not import `ConcreteCCM25ArithmeticPackage`,
`SourceRouteTraceData`, or the broad `ForAllTests` certificate.

## Verdict

```text
fixed-detector type owner: pass
broad package bypass: pass
local exact-support consumer: pass
actual source fields for Xi detector: open
CC20/M4 same-test sign bridge: open
```

Plan 028 survives the cheapest type-level death gate. The next work is
mathematical construction of the local `qwDefinition`, `qwLambdaFormula`,
`poleNormalization`, and CC20 trace fields for the Xi/M4 detector.

