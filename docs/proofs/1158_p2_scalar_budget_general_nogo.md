# Record 1158 — General P2 scalar-budget no-go

Date: 2026-09-06

## Result

`C1P2BudgetNoGo.lean` proves the generic theorem
`not_p2OneWindowBudgetWitness_of_healthyDetectorData`:

```text
HealthyYoshidaDetectorData rho g
  ∧ P2OneWindowBudgetWitness g
  -> False.
```

The proof uses only the existing canonical P2 consumer.  A scalar witness
would imply the orbit-window gate and therefore `qw(g) ≥ 0`; the healthy
detector's local-Weil field independently implies `qw(g) < 0`.  The argument
is independent of the chosen reference window and uses no numerical estimate.

## Route meaning

This is a FORMAL no-go for the entire absolute-value one-window budget family,
not for P2 itself.  It rules out continuing by changing `W` or its support
radius while retaining the same Stage-B budget shape.  The remaining viable
P2 targets are a signed bilateral-profile inequality or a new same-owner
semi-local trace comparison.  P2 and RH remain OPEN.

The owning and audit modules build successfully in 3660 jobs.  The audited
declaration uses only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.
