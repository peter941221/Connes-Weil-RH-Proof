# 2889 Route B D4 Cauchy interval enclosure

The right endpoint Cauchy circle at radius `0.05` is split into angular
rectangles and evaluated with `mpmath.iv`. The hyperbolic tangent is represented
as `(exp(2a)-1)/(exp(2a)+1)`, so the enclosure uses interval elementary
operations throughout.

The artifact records the resulting rectangle upper bounds. It is an analytic
enclosure input, but the final Cauchy remainder theorem and its connection to
the stored Taylor coefficients are still separate obligations.
