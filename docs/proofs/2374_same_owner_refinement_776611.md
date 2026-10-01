# 2374 - Same-owner 776611-node refinement

日期：2026-10-02。

The same-owner 2242 evaluator and 256-bit directed pointwise path were rerun
at 776611 nodes with the fixed 20001-node spans. The directed readings remain
stable to displayed precision:

```text
2.6867143296475287
8606.21439765068
90.78788225375546
125446.71132157759
```

Under the existing 2348 second-derivative remainder price, `corr_D2` is now
approximately `12544.629302232996`, or `0.0999996666` of the directed
`corr_D2` reading. This meets the pre-registered 0.1 refinement target and
shows a usable numerical margin under the same owner. It remains a numerical
refinement artifact: the exact node upper import, Lean numerical bridge, and
full trapezoid certificate are still open.

Status: `SAME_OWNER_REFINEMENT_0_1_PRICE_CONTROLLED`; producer GO: `false`.
