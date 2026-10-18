# 2876 Route B D4 residual H margin

After correcting the centered logistic normalization, the residual polynomial
`H(t,z)` has the expected signs along the owner path:

```text
u interval                 H range (sampled)
[1/4096, 0.1353]           [ 0.011989, 127.438]
[0.1354, 0.3028]           [-6.91448, -0.001283]
[0.3029, 1/2]              [ 0.010386, 13]
```

The middle interval has a usable sampled margin. The outer intervals remain
close to zero at their endpoints, so the formal proof should use endpoint
factor extraction or a monotonicity argument rather than a uniform margin.
This is a high-precision owner-path diagnostic, not a sign certificate.
