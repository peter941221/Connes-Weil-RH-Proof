# 2865 Route B full sharp-e0 model reprice

This run applies the Lean-certified sharp initial box `[1/16,1/8]` to all 8192
Route B cells in the Python interval evaluator and sums the replay-owned D4/D7
cell charges. It is a global model pricing artifact used to decide whether the
next Lean assembly is economically viable; it is not a Lean full-cell proof or
ledger domination theorem.

Readout:

```text
order | sharp replay-owned sum | target | ratio
------+-------------------------+--------+------
4     | 4211.41340390119       | 1500   | 2.807608936
7     | 1042199618.52014       | 2e9    | 0.5210998093
```

The D4 model charge is above the existing 1500 target by about 2.81x, while
the D7 model charge remains below its 2e9 target. Therefore the existing
two-order aggregate cannot yet be consumed: D4 needs a tighter enclosure,
an explicitly re-priced target, or a changed mathematical decomposition.
This is a pricing decision, not a proof of impossibility and not a global
Lean result.
