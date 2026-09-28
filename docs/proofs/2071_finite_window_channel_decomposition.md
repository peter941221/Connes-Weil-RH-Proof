# 2071 - Finite-window signed channel decomposition

Date: 2026-09-28.

Status: FINITE-WINDOW-SIGNED-CANDIDATE.

The actual one-copy G8-H owner was evaluated on the same finite visible-prime
book (`1647` entries) and the same `|xi| <= 40` window. The signed kernel was
split into its archimedean sigma contribution and the visible-prime cosine
contributions, while retaining the common owner weight `h(xi)`.

```text
step       sigma                  prime_total             total
0.020   -2.347126326466648e14    2.313065827948812e14   -3.406049851783656e12
0.010   -2.347126326466652e14    2.313065827948815e14   -3.406049851783688e12
0.005   -2.347126326466652e14    2.313065827948840e14   -3.406049851781156e12
```

The total is stable under the three grid refinements at approximately the
`1e-9` relative scale. The prime contribution is strongly cancellation-led:
the sum of absolute prime-channel integrals is about `1.229773810811e15`,
roughly `361` times the magnitude of the signed total. The largest individual
prime component is about `9.44134339984756e13`.

Decision: `FINITE-WINDOW-SIGNED-CANDIDATE`. This justifies continuing with a
direct signed quadrature enclosure for the aggregate kernel. It does not
prove the finite-window value: the readings are composite trapezoid values,
and the source-transform, coefficient, arithmetic, and model-to-real errors
are not included.

The next certificate must enclose the aggregate integrand or its quadrature
error as one signed object. Bounding each prime channel independently and
then summing absolute values would erase the observed cancellation and is not
an acceptable replacement.

Artifact: `results/2071_finite_window_channel_decomposition.json`.
Script: `scripts/routea_finite_window_channels_2071.py`.