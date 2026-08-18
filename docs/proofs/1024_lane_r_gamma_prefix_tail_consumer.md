# 1024 - Lane R Gamma_R prefix/tail sign consumer

Date: 2026-08-18.

## Verdict

The finite-prefix and shifted-tail interfaces are now formally coupled.  A
finite prefix bound with margin `budget`, together with an absolute tail norm
at most `budget`, implies nonpositivity of the complete same-owner
archimedean term.  A strict prefix margin gives strict negativity.

This is a consumer theorem.  It does not prove the finite constrained-kernel
inequality or global Lane R; the prime-inclusive case and RH remain open.

## Lean Owner

`ConnesWeilRH/Dev/C1XiCenterTwoGammaPrefixTailConsumer.lean` uses the exact
decomposition from `C1XiCenterTwoGammaSummedKernel`:

```text
archimedeanTerm(F)
  = constant(F) + finitePrefix(F,N) + Re(tail(F,N)).
```

The elementary complex estimate
`Re(tail(F,N)) <= ||tail(F,N)||`, followed by
`norm_gammaRArchProfileTail_le_tailNorm`, turns the tail norm producer into a
real upper bound.  The public non-strict consumer is
`archimedeanTerm_nonpos_of_profilePrefix_bound_and_tailNorm_bound` and assumes

```text
constant(F) + finitePrefix(F,N) <= -budget
tailNorm(F,N) <= budget.
```

The strict companion
`archimedeanTerm_neg_of_profilePrefix_bound_and_tailNorm_bound` replaces the
first line by `<= -(budget + delta)` with `delta > 0`.

## Scope Boundary

The theorem is an order-theoretic assembly step, not a numerical certificate.
The missing producer is still a finite constrained-prefix inequality on the
same triple-vanishing owner.  The explicit rate in proof 1023 supplies a
candidate tail budget, but choosing a useful `budget` and proving the matching
prefix margin remain open.

## Verification

WSL2 ext4 owner/probe verification completed at 3541 jobs and reported only
the standard project axioms:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, numerical eigenvalue, unconditional RH theorem, or project root
axiom is used.
