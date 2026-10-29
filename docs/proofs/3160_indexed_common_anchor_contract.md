# 3160: indexed common support anchor contract

Date: 2026-10-29.

Status: Lean-verified contract audit. This record does not construct the
indexed producer, replace the legacy root, or claim SourceRH/RH.

## Result

Added `ConnesWeilRH/Dev/IndexedProducerFixedPoint3160.lean`.

The module fixes the ambient non-degenerate common pair and proves that the
existing `FixedLambdaSourceWeilFormVisibleArithmeticData.toSupportData` path
returns global and restricted support data whenever the explicit anchor is
provided:

```text
ambient source Weil form
        + commonAnchor
        + lambda > 1
        -> common finite-prime support data
        -> global/restricted index readbacks
```

The ambient probe does not prove the anchor. Its `common` field is the chosen
compact bump, while the CCM25 common-test path expects the encoded common to be
the convolution square of the test. The module therefore keeps the equality
as an explicit hypothesis instead of using `rfl`.

## Boundary

This closes only the common-pair support construction under an anchor. It does
not provide the arbitrary `(f, g, lambda)` indexed certificate family needed
by `IndexedCommonFinitePrimeArithmeticSourceData`. The next producer target is
therefore the arbitrary-pair analogue of the anchor and support readback, not
another constructor wrapper.

## Verification

```text
lake build ConnesWeilRH.Dev.AmbientSourceWeilFormSeam
lake env lean ConnesWeilRH/Dev/IndexedProducerFixedPoint3160.lean
```

The development module checks successfully with the Linux-side Lean 4.30
toolchain. Only existing linter warnings about unused explicit anchor
parameters remain; no Lean error was reported.
