# 2138 - Route-A residual-budget consumer contract

Date: 2026-09-28.

Status: FORMAL-CANDIDATE, NOT BUILD-VERIFIED IN THIS WINDOWS WORKTREE.

## Purpose

The old Route-A consumer required exact interpolation zeros on every source
zero in the low-shell closed-ball owner. That requirement makes the Jensen
cardinality bound directly control the interpolation dimension. Record 2138
adds the consumer-side budget split needed by an owner-local construction:

```text
selected finite prefix
    + omitted low-shell real-part residual
    + high-shell absolute norm tail
    < anchor multiplicity
```

## Formal interface

`spectralWeilValue_neg_of_finite_prefix_residual_and_tail` in
`ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean` accepts:

1. a finite `S` inside `spectralHeightShellPrefix N`;
2. a signed prefix bound on `S` at most `-xiMultiplicity rho`;
3. a real residual budget `delta` for
   `spectralHeightShellPrefix N \ S`;
4. a strict high-shell norm-tail bound below
   `xiMultiplicity rho - delta`.

The theorem is only the exact shell algebra. It does not provide the
residual budget, owner construction, finite-window C3' margin, or actual-owner
transfer. Those remain the Go obligations.

## Verification boundary

The paired audit was extended with `#check` and `#print axioms`. The current
Windows checkout has no Lean/Lake executable, while the available WSL project
copy is stale and contains unrelated uncommitted changes. Therefore no build
claim is made in this record. The staged source passes `git diff --check` only.

## Decision

This is a strictly smaller consumer obligation, not a Route-A Go result. The
next admissible experiment must price the omitted-node residual on an explicit
owner model. If that residual cannot fit inside `delta`, this interface should
be closed for that owner class with a numerical margin record.
