# 3222: Route A concrete-owner uniform second and fourth bounds

Status: verified analytic bounds; these are interface bounds, not yet the
final cancellation-preserving numeric budget.

The file proves order-2 and order-4 bounds for the actual `record2680` owner
using the same 2538 family envelope as the verified sixth-order proof. The
real derivative bounds are obtained from the complex 30-family sum by taking
the real-part norm.

Exported bounds:

```text
record2680_uniform_second_bound3222
record2680_uniform_fourth_bound3222
```

Both bounds are nonnegative and cover every diagnostic-grid index and every
coordinate. The proof is same-owner and does not import JSONL rows.

Verification: WSL2 ext4, `leanprover/lean4:v4.30.0`, Lean `4.30.0`, focused
build and axioms audit. The audited declarations use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Important limitation: the bounds use conservative full-support geometry. They
close the Taylor interface, but the final negative aggregate may require
cell-local near/far geometry to preserve the diagnostic margin.
