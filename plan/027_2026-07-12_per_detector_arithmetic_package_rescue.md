# 027 Per-Detector Arithmetic Package Rescue

Date: 2026-07-12

Status: new research candidate after the scoped death in proof 094.

## Idea

Do not rebuild the universal `SourceWeilFormData` over every ambient Schwartz
test. For the Xi/M4 detector choose one compact witness `f` and one cutoff
`lambda`, then construct only the route-facing package

```text
ConcreteCCM25ArithmeticPackage W f lambda
```

The repository already exposes `FinitePrimeExact.ExactSupportAtLambda W f f
lambda` and package constructors whose support certificate is tied to this
fixed common test.

## Why this may survive 094

The finite prime set only needs to cover the selected convolution square, whose
compact log support makes the visible prime powers finite. No claim is made
about arbitrary noncompact Schwartz tests. The ambient Schwartz carrier remains
useful for linear combinations, while the package certificate is local to the
chosen compact detector.

## Required gates

1. Define `W.convolutionStar` as the genuine ambient Schwartz convolution and
   prove the compact witness square transport from proof 091.
2. Build the fixed-test `ConcreteCCM25ArithmeticPackage` using the existing
   `FinitePrimeCertificate` rows, with no universal `SourceFinitePrimeData`
   conversion.
3. Prove the package's `psi`, pole, and prime read-offs for that same square.
4. Transport the CC20 support-square trace and M4 bad-space rows to the same
   ambient test.
5. Combine with the Xi orbit/bad-space finite functional separation.

## Cheapest death gate

Check whether package construction secretly requires the broad
`SourceWeilFormData` root or can be made directly from fixed-test certificate
rows. If it requires the broad root, Plan 027 dies with proof 094. If not, the
route has a genuine per-detector owner candidate.

