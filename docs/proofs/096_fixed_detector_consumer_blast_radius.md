# 096 Fixed-Detector Consumer Blast Radius

Date: 2026-07-12

## Evidence

The broad package is deeply embedded in the current route. `Bridge.lean`
references `ConcreteCCM25ArithmeticPackage` throughout the package read-off,
finite-prime sign, source-QW common-test, and exhaustion bridge layers. The
existing `SourceQWUsesCommonTest` structure requires
`PackageBackedCCM25WeilFormReadOff`, which itself requires the broad package.

Therefore Plan 028 cannot be implemented by replacing one constructor. It needs
a parallel fixed-detector consumer chain.

## Recommended narrow owner

Define a new data record, outside the current broad package:

```text
FixedDetectorWeilData f lambda where
  square                 : TestFunction
  square_eq_convolution  : square = W.convolutionStar f f
  exactSupport           : ExactSupportAtLambda W f f lambda
  poleReadOff            : local pole formula on square
  primeReadOff           : local finite-prime formula on exactSupport
  qwReadOff              : one-test QW formula
```

Then define a detector-specific sign bridge consuming this record plus the
CC20/M4 same-test trace. Do not coerce it into
`ConcreteCCM25ArithmeticPackage`; that would reintroduce `ForAllTests`.

## Decision

```text
mathematical local owner: plausible
current route compatibility: absent
rewrite size: broad consumer parallel chain
cheap contradiction: none yet
```

This is an architectural route fork, not a routine edit. The first proof
target is a standalone fixed-detector contradiction theorem whose only
arithmetic premise is `ExactSupportAtLambda`; if that theorem cannot be stated
without importing the broad package, Plan 028 dies.

