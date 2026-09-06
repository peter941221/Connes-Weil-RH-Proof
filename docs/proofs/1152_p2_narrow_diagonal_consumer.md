# Record 1152 — P2 narrow diagonal consumer

Date: 2026-09-06

## Result

`C1P2NarrowDiagonalConsumer.lean` adds a FORMAL conditional consumer for the
two diagonal gates from record 1151.  For any `F`, if the convolution-square
test is supported in `(-R,R)` with `R < log 2`, then its finite visible-prime
sum is zero.  Combining this prime-free reduction with
`archimedeanTerm_nonpos_of_narrow_budget` gives

```text
log(4π) + γ + R - 1/2 log(1/R) ≤ 0
  ⟹ ICgate(F□) ≤ 0.
```

Instantiating the result for an even `f` and an odd `g`, together with the
triple-vanishing hypothesis for `f + g`, feeds the existing even/odd gate
consumer and proves `qw(f + g) ≥ 0` under the two narrow-support and budget
contracts.

The companion theorem `cc20TripleVanishes_of_even_odd_nodal` removes the
repeated interface proof: oddness kills the zero node, while the supplied
`1/2` and `1` nodal sums close the other two members of
`cc20TripleFiniteVanishingSet`.  The resulting
`qw_nonneg_of_even_odd_nodal_narrow_diagonal` consumes exactly those three
node equations.

The owning and audit modules build successfully in 3685 jobs.  The audited
declarations use only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This is a FORMAL sufficient-condition brick, not a proof that the pinned
right-oriented orbit detector has narrow convolution-square support or meets
the budget.  No theorem currently maps that rho-specific detector into this
narrow class, so P2/C3 remains OPEN and RH is not claimed.
