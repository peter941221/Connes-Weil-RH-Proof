# Record 2730: analytic endpoint and derivative bounds

Task card: owner = smoothSeed and exact Real.smoothTransition.
Target = D4 <=1500 and D7 <=2e9 for the 2729 split envelope.
Consumer = poweredSeed strip envelope, not a new RH exit.
Budget = one 8192-cell order-7 integration, <=10 minutes, <=1 GiB RAM,
no bulk Lean generation. Stop if either bound fails; no refinement
or automatic extension. Completion = exact rational interval upper
endpoints plus explicit analytic endpoint derivation, then state the
remaining Lean obligations. No neighboring-cell safety proxy.


## Endpoint derivation, from product rules

Let x be real with 0<x<=1/2, F(x)=-1/x+1/(1-x),
E(x)=exp(F(x)), R(x)=1/(1+E(x)), and T(x)=E(x)R(x).
All functions are smooth on that open interval. E is positive and E<=1;
0<R<=1. The absolute derivative bounds below avoid any complex analysis.
For j>=1, direct differentiation gives

```text
|F^(j)(x)| <= j! (x^(-j-1) + (1-x)^(-j-1))
           <= 2 j! x^(-2j).
```

The second inequality uses x<=1-x and j+1<=2j. Define integer sequences:

```text
b_0 = c_0 = 1
b_(k+1) = sum_(j=0..k) binom(k,j) 2(j+1)! b_(k-j)
c_k     = sum_(j=1..k) binom(k,j) b_j c_(k-j)       (k>=1)
d_k     = sum_(j=0..k) binom(k,j) b_j c_(k-j).
```

Differentiate E'=F'E for the first recurrence. Differentiate
(1+E)R=1 for the second; isolate R^(k) and divide by 1+E>=1.
Since E<=1, induction gives

```text
|E^(k)| <= b_k E x^(-2k)
|R^(k)| <= c_k x^(-2k)
|T^(k)| <= d_k E x^(-2k).
```

For a=1/4096 and 0<x<=a, E<=exp(2)exp(-1/x)<8 exp(-1/x).
The derivative of x^(-2k)exp(-1/x) has the sign of 1-2kx,
so it is increasing on this endpoint region for k<=7. Using exp(1)>2:

```text
4 integral_0^a |T^(k)|
  <= 32 d_k a^(1-2k) exp(-1/a)
  <= 32 d_k a^(1-2k) 2^(-4096).
```

This is an analytic bound over the entire missing region, not a sampled
comparison. The exact rational on the last line is added to each directed
interval sum. Reflection T(1-x)=1-T(x) supplies the other endpoint.
The seed-to-transition factor is 4 on the half interval, matching the
existing whole-line seed ladder and reflection reduction.

## Finite-region arithmetic

The 8192 cells partition [1/4096,1/2] at exact dyadic coordinates.
The jet operations use directed interval arithmetic at 40 decimal digits,
with products and accumulations kept as intervals. The upper endpoint of
the final interval is decoded to an exact rational before adding the
analytic endpoint charge. Decimal values in the artifact are diagnostics;
its rational values and integer recurrences carry the bounds.

The jet algorithm comes from the unchanged 2720 engine. Its product,
reciprocal and exponential recurrences still need Lean correctness proofs
before this can discharge `derivOrderL1` hypotheses. Interval evaluation
alone does not prove that a program computes derivatives of the Lean T.


## Landed bounds and consumer check

Six in-run checks passed. Exact rational readback confirms both targets;
separate checks verified the outward endpoint decoder against 1/3,
exact dyadic cell width, endpoint coverage at 1/2, integer recurrence
positivity and current checker/parent hashes.

```text
order   directed-sum + analytic-endpoint upper    chosen proof target
4       1400.650853119245                         1500
7       592705254.0438685                        2000000000
```

The decimal display is approximate; comparisons with the integer targets
use exact rational arithmetic. Both endpoint charges are <10^(-1000).
Orders 1 and 2 contain their known exact masses; order 3's enclosure is
81.06976465, consistent with the existing narrow Lean bracket near 78.72833845.

Consumer feasibility, conditional on the same stored-model constants:
D4<=1500 is tighter than the finite-scan D4=1535.125524, while the
existing Lean bounds for orders 1-3 are tighter than that scan's inputs.
The finite envelope therefore cannot increase, by monotonicity of each
rung and their min. For the exterior, all 2729 correction terms used rung7;
changing D7 scales that bound by the tenth power. Conservatively round
its old bound up to 6.257e-8 and old D7 down to 1.103e9:

```text
new_C2_tail <= 6.257e-8 * (2e9 / 1.103e9)^10 < 1e-4 < 2.9e7.
```

This is exact-rational target repricing, not another scan or a claim
that stored-model constants have become formal. Base C4 and q tails can
retain the fourth-order bound already priced in 2729.

## What is still not proved in Lean

1. The smoothTransition formula and derivative-jet interpretation at all
   orders through seven, tied to the source function on (0,1).
2. The b/c/d derivative inequalities and the endpoint monotonicity bound.
3. Import/replay of interval inequalities and the integral partition into
   the seed ladder theorem. The rational artifact alone is not a theorem.
4. The finite envelope/cell proof, model-constant ownership, poweredSeed
   carrier, and genuine-rho gate/interpolation duties from 2729 remain.

Recommended next formal target is the generic derivative recurrence on
(0,1), because proving it establishes what every jet slot means. Do not
start thousands of cell modules before this semantic bridge exists.
No RH producer premise has been discharged by this run. Exact mass 3
and existing order-1..3 theorems are unchanged.
