# Record 1166 — P2 explicit-range witness contract

Date: 2026-09-06

## Result

`P2BilateralProfileRangeWitness g B` stores the single real inequality over
`range (ceil(exp B)+1)`.  The theorem
`P2BilateralProfileRangeWitness.toAggregate` uses the support-controlled
finite-range readback to convert it into the exact aggregate witness for `g`.

The focused owner/audit build completed successfully in 3721 jobs.  The audit
uses only `[propext, Classical.choice, Quot.sound]`, with no `error:` lines and
no `sorryAx`.

## Route meaning

The pinned orbit construction already supplies the source support radius
`n+2` and hence the square cutoff `B = 2(n+2)`.  The remaining P2 task is now an
explicit signed finite-range estimate (or an equivalent positive-trace
readback), not support bookkeeping.  P2/RH remain OPEN.
