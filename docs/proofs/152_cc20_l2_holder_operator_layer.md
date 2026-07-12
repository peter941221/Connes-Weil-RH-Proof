# CC20 L2 Holder operator layer

On `cc20CompactMeasure`, the same kernel section and continuous input have a
pointwise Holder estimate:

```text
|T f(x)| <= ||K(x,.)||_2 ||f||_2.
```

The input square-root integral is formally identified with both `lpNorm f 2`
and the norm of `ContinuousMap.toLp 2 cc20CompactMeasure ℝ f`. The output map
is continuous in `x`, additive, homogeneous, and is packaged as the linear map
`cc20CompactMeasureToLpLinearMap` into `Lp ℝ 2 cc20CompactMeasure`.

The remaining estimate is to integrate the pointwise output bound over `x`
and obtain one global `L2` operator constant. Until that is proved,
`LinearMap.extendOfNorm` cannot be used for a full `L2` extension. No CC20
source action identity or RH conclusion is claimed.
