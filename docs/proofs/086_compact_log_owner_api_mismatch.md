# 086 Compact Log Owner API Mismatch

Date: 2026-07-12

## New evidence

The repository already contains a genuine compact multiplicative carrier in
`ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean`:

```text
CompactLogTest
  test            : SchwartzMap ℝ ℂ
  compactSupport  : HasCompactSupport test
CompactLogTest.involution
CompactLogTest.convolution
CompactLogTest.convolutionSquare
```

The file proves support-preserving reflection/conjugation, additive log
convolution, Hermitian square symmetry, and nonnegative square value at zero.
Its convolution is the genuine integral

```text
(f * g)(x) = integral t, f(t) * g(x - t).
```

This is the correct carrier for finite complex witness combinations and avoids
the invalid additive toy model.

## API mismatch

`SourceTestAlgebra` currently requires `legacy : LegacyTestEquiv Test`, where
`LegacyTestEquiv` is a bijection with all `TestFunction = SchwartzMap ℝ ℂ`.
A compact-support carrier cannot satisfy this: most Schwartz functions are not
compactly supported. The existing interface cannot host `CompactLogTest`
without either storing an invalid inverse or weakening the API.

## Minimal repair shape

Split the old equivalence into two roles:

```text
SourceCarrier:
  Test -> TestFunction        (injective encoding)
  finite linear structure
  convolution/involution

SourceCompactWitness:
  chosen compact-support test
  support and smoothness proofs
```

Legacy full surjectivity should remain only for APIs that genuinely need every
Schwartz function. The Xi/M4 route needs the forward encoding and finite linear
combinations of compact witnesses, not a decode of arbitrary noncompact
Schwartz functions.

## Gate result

```text
genuine compact convolution owner: exists in repository
Mellin/Fourier normalization bridge: still open
old SourceTestAlgebra compatibility: fails structurally
required next action: API-level owner redesign, no theorem conclusion stored
```

This is a design blocker, not a mathematical rejection of the Xi/M4 route.

