# 2373 - Same-owner 347311-node refinement

日期：2026-10-02。

The same 2242 evaluator, owner, sigma, fixed span size, and directed MPFR
pointwise path were rerun at 347311 nodes. The four directed readings remain
stable to displayed precision:

```text
2.6867143296475287
8606.21439765068
90.78788225375534
125446.71132157731
```

Using the same 2348 second-derivative price, the `corr_D2` panel remainder
scales from `131353.39607658036` at 240001 nodes to approximately
`62723.34531294934`, a ratio `0.4999999175` against the refined directed
`corr_D2` reading. This validates the refinement scaling and keeps the
obligation same-owner; it does not yet import a node certificate or prove the
trapezoid remainder in Lean.

Status: `SAME_OWNER_REFINEMENT_PRICE_CONTROLLED`; producer GO: `false`.
