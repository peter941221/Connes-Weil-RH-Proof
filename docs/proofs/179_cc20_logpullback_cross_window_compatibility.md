# Proof 179: cross-window compatibility on the source tests

## Route obligation

Connect the complete fixed-window common-carrier operators to the actual
compact source tests used by the RH route.

## Result

`GlobalLogKernel.lean` now proves that every `cc20LogPullback p` has an exact
common-carrier representation in any logarithmic window containing its support.
The proof uses the source test's already-proved continuity and compact support,
constructing a bounded continuous function with
`ofCompactSupport` and comparing the two `MemLp.toLp` representatives.

For `1 < lambda ≤ mu`, if the source support is contained in the smaller
window, Lean proves the correct compressed compatibility identity:

```text
P_lambda (T_mu (cc20LogPullbackLp p))
  = T_lambda (cc20LogPullbackLp p).
```

This is intentionally a projected equality.  The unprojected outputs for
different windows need not be equal because the larger-window output can have
nonzero values outside the smaller window.

## Verification

Using the retained WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

The aggregate build passes (`3497/3497`).  The focused declarations print only:

```text
propext
Classical.choice
Quot.sound
```

No RH premise, stored conclusion, `sorry`, `admit`, or `axiom` was introduced.

## Boundary

This is source-test compatibility, not strong operator convergence on all of
global `Lp`.  The remaining route obligations are a common uniform control
space, the diagonal distributional `-2 Dirac_0 -> -2 Id` limit, the same-test
CC20 trace read-off, and rewiring the final unconditional RH consumer.
