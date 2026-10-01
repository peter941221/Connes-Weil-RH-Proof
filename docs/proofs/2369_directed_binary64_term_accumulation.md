# 2369 - Directed accumulation of binary64 nodal terms

日期：2026-10-02。

The 2359 evaluator now accumulates every generated binary64 point term with
256-bit MPFR `RNDU` inside each fixed 20001-node span, resets the accumulator
for every reused worker span, combines span upper bounds in increasing span
order with `RNDU`, and multiplies by the positive binary64 `dx` with `RNDU`.
The full 240001-node run gives directed term-accumulation upper values:

```text
2.6867143296475287
8606.214397650678
90.78788225375544
125446.71132157759
```

This is a real directed accumulation result for the already-generated
binary64 point terms. It does not certify that `interval_abs_upper` itself is
the exact directed upper of the underlying interval expression, and it does
not include the composite-trapezoid remainder. Therefore it remains a
conditional numerical bridge, not a nodal producer certificate or GO.

Status: `DIRECTED_BINARY64_TERM_ACCUMULATION_ONLY`; producer GO: `false`.

This layer is superseded for the live replay by record 2370, which performs
the rectangle norm and exponential construction in MPFR before accumulation.
