Record 2537: weighted external-family derivatives
Date: 2026-10-03

The local order-0..4 bump envelope from 2536 now applies to the existing
weighted external-family function. The proof retains the signed modulation
in the complex derivative multiplier. It takes a norm only when bounding
the derivative magnitude.

Let sigma be the real exponential weight, theta the signed modulation,
c the complex coefficient, r>0 the support radius, and B_r the existing
smooth widthBump function. Define lambda=sigma+i*theta, where i is the
imaginary unit. The exact owner identity is

```text
weightedFunction2348 sigma (externalFamilyValue2344 c theta r)(x)
  = c * exp(sigma*x) * exp(i*theta*x) * B_r(x).
```

The theorem weightedExternalFamily_eq2537 proves this equality on the
existing definitions. The derivative theorem applies the product rule to
that same function, for every derivative order n:

```text
D^n F(x) = c * sum_(j=0..n) choose(n,j)
             * D^j[exp(sigma*x)*exp(i*theta*x)] * D^(n-j) B_r(x)

D^j[exp(sigma*x)*exp(i*theta*x)]
          = lambda^j * exp(sigma*x)*exp(i*theta*x).
```

For n<=4, weightedExternalFamily_iteratedDeriv_le_local2537 substitutes
localCoupledBumpUpper2536 for each actual bump derivative. Its geometric
inputs are near<=|x/r|<=far and 0<=near<1. No derivative-magnitude premise
or precomputed numerical bound appears in this theorem.

The exact identity uses sigma+i*theta, not |theta| in the complex phase.
Both endpoint signs and negative modulations therefore share one theorem.
The proof also retains the existing smooth zero extension at |x|=r.

Evidence:
ConnesWeilRH/Dev/C1RouteAWeightedFamilyLocal2537.lean
ConnesWeilRH/Dev/C1RouteAWeightedFamilyLocal2537Audit.lean
results/2538_weighted_cell_validation.json

Record 2538 converts this pointwise formula into the explicit cell bound
needed by 2535. Numerical evaluation, coefficient-box import and exact-owner
transfer remain separate obligations.
