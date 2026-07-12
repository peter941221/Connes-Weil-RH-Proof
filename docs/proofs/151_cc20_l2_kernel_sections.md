# CC20 kernel sections in L2

With the explicit finite measure on `[1/2,2]`, every fixed-output-point
section

```text
y |-> K(x,y)
```

is a continuous function on the compact interval and therefore belongs to
`MemLp ... 2 cc20CompactMeasure`. Every continuous input function has the same
`L2` membership. The section norm is bounded by the compact kernel supremum
norm.

These are the exact measurability and integrability premises needed for the
next Holder/Cauchy--Schwarz estimate. They do not yet prove the integral
operator's `L2` norm bound or an RH consequence.
