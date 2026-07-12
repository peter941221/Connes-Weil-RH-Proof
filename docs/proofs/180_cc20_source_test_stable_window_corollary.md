# Proof 180: stable compressed window for every source test

## Result

`GlobalLogKernel.lean` now packages the source-test exhaustion and the
cross-window compressed compatibility into one theorem:

```text
∀ p, ∃ lambda > 1, ∀ mu ≥ lambda,
  P_lambda (T_mu (cc20LogPullbackLp p))
    = T_lambda (cc20LogPullbackLp p).
```

The proof chooses the logarithmic window already supplied by
`exists_cc20LogWindow_containing_logPullback`, then applies the same-object
source-test compatibility theorem for every larger cutoff.

This is the exact stability statement needed before taking a source-test trace
limit. It deliberately does not claim unprojected equality of the larger and
smaller outputs.

## Verification

Using the retained WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

Both pass (`3497/3497`). The new declaration has only:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, `axiom`, or RH-level premise was introduced.

## Boundary

This is a source-test statement, not strong convergence of `T_lambda` on all
global `Lp`. It does not supply the uniform three-point bad-space estimate, the
diagonal distributional identity, or the same-test CC20 trace read-off needed
to rewire the unconditional RH consumer.
