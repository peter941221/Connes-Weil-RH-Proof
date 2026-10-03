Record 2556: signed endpoint values reuse derivative replay

The order-zero signed bounds at nodes2700,2701,5440 and10239, at both
sigma signs, now consume the existing kernel node's BaseError2555 proofs.
Each of the eight new modules references all thirty parent family proofs;
none contains a new exponential evaluation. The exact centers and errors
are the parent's 160-bit payload, and the same error also feeds its
order-three derivative certificate. An endpoint proof can therefore be
used by either neighboring cell without repeating its exponential replay.

The signed center sum is formed before taking the complex norm. Evaluation
error and the existing coefficient uncertainty remain charged. The actual
coefficient-ball membership remains an explicit premise of each physical
function bound.

```text
+-------+----------------------+----------------------+
| Node  | sigma = +1/2 upper   | sigma = -1/2 upper   |
+-------+----------------------+----------------------+
|  2700 | 179/2000000000       | 19793/10000000000    |
|  2701 | 873/10000000000      | 9637/5000000000      |
|  5440 | 721605217/1250000000 | 766536121/2000000000 |
| 10239 | 1/5000000000         | 1/5000000000         |
+-------+----------------------+----------------------+
```

All six previously accepted order-zero upper constants are reproduced
exactly. The negative-sign boundary nodes provide two additional signed
value bounds. This does not add a whole-cell or continuous-segment bound.

Generate with scripts/generate_shared_values_2556.py. Build the project
root and the eight C1RouteASharedN...2556 modules in the Linux verification
environment; validate with scripts/validate_shared_values_2556.py using
--mirror PATH and --log PATH. The generator's old adaptive defaults and
the four accepted adaptive reader cases remain regression anchors.

The independent reader derives each 160-bit trace from the actual support
geometry, checks parent payload equality and recomputes the signed sum.
Zeroing any final upper is rejected. That test exposed a missing sign
check in the older reader: before using (upper - allowance)^2 as a norm
bound, upper - allowance must be nonnegative. A negative number can have
a large positive square, so squaring alone was insufficient at tiny edge
values. The reader now checks this prerequisite explicitly; no accepted
Lean bound or numerical value changed.

The first proof template used a tactic combinator that produced style
warnings on interior cases. Replacing it by a single-goal tactic left a
second equality open in exterior cases. The final template explicitly
normalizes all conversion goals, handling both support branches without
weakening a statement or suppressing a linter.

Evidence: results/2556_shared_value_inputs.json and
results/2556_shared_value_readback.json. Remaining work is a new neighboring
cell, shared endpoint norms, the new midpoint/fourth envelope and their
continuous-segment sum, followed by full-grid and exact-owner obligations.
