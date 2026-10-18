# 2878 Route B D4 residual monotonicity diagnostic

The owner-path derivative scan gives:

```text
u interval                 dH/dt range (sampled)
[1/4096, 0.1353]           [-1197.96, -125.78]
[0.1354, 0.3028]           [-125.52, 85.15]
[0.3029, 1/2]              [0, 85.73]
```

Both outer regions are sampled-monotone, while the middle region has one
turning point. This makes the next formal target concrete: prove the derivative
sign on the outer regions, then use the endpoint identities from 2877. The
scan itself is not a monotonicity or sign certificate.
