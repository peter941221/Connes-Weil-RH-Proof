# 095 Per-Detector Package Hidden Universal Quantifier

Date: 2026-07-12

## Death of Plan 027

`ConcreteCCM25ArithmeticPackage W f lambda` appears fixed-test because its
outer parameters include `f` and `lambda`, but its `rows` field is

```text
Interface.ConcreteCCM25ArithmeticRows W
```

and `Rows.ConcreteCCM25ArithmeticRows` contains

```text
FiniteLambdaArithmeticSourceTestCertificatesForAllTests W
```

which expands to

```text
∀ f g : TestFunction,
  ∀ lambda, 1 < lambda -> FixedLambdaFinitePrimeArithmeticCertificate W f g lambda.
```

Therefore package construction still requires the universal finite-prime
certificate over the whole ambient Schwartz carrier. The outer fixed detector
does not lower that quantifier.

## Decision

```text
Plan 026 broad source core: dead
Plan 027 apparent per-detector package: dead by hidden universal field
Plan 028 direct fixed-detector certificate consumer: open
```

The ambient convolution probe remains valid evidence, but it cannot be wrapped
in the current `ConcreteCCM25ArithmeticPackage` without reintroducing the
invalid universal source rows.

