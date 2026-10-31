# 3221: Route A aggregate adapter with uniform sixth bound

Status: verified adapter; the aggregate is still conditional on value,
second-derivative, and fourth-derivative arrays.

`C1RouteAConcreteOwnerAggregateWithUniformSixth3221.lean` applies the fixed
40960-cell aggregate theorem from 3213 while supplying the sixth-derivative
array and its nonnegativity from 3220.

The remaining hypotheses are now exactly:

```text
valueUpper[index]
secondUpper[index]
fourthUpper[index]
```

for every `index < 40960`. No sixth-derivative premise or external JSONL row
is required by this adapter.

Verification was performed in WSL2 ext4 with Lean `4.30.0` and
`LEAN_NUM_THREADS=1 lake build`. The audit for
`intervalIntegral_record2680_40960_aggregate_upper_with_uniform_sixth3221`
reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```
