# Record 3265: Cell-17168 Families 10-14 Positive Phase Block

Status: support no-go for the proposed negative block.

The 3244 screen used the legacy `jets[0]` path whose first returned value is
the weighted second derivative. That diagnostic cannot establish the sign of
the formal weighted original function. The corrected 3238 evaluator and the
3264 phase boxes identify the actual coefficient-phase block for families
10 through 14.

Lean proves a conservative lower bound for the exact block rectangle:

```text
coefficient-phase block 10..14 >= 200000000000000000
```

Therefore the block is strictly positive. Since the 3263 factorization has
positive exponential weight and positive shared bump at 17168, this block
cannot be the negative signed contribution needed by the current producer
budget. Keep the phase boxes as reusable infrastructure, but do not pursue a
negative upper bound for this family grouping.
