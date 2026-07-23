# Proof 512: uniform scalar-normalized Julia transition bound

## Result

Proof 512 discharges the transition-bound contract introduced by Proof 511.
For every visible prime `p` and suffix `S`, Lean proves

```text
||rho_p^(-1) * transition(p,S)|| <= 8,
rho_p = (1 - p^(-1/2)) / (1 + p^(-1/2)).
```

The argument is elementary and exact:

```text
p > 1
  -> p >= 2
  -> p^(-1/2) <= 3/4
  -> rho_p >= 1/8
  -> ||transition(p,S)|| <= 1
  -> ||rho_p^(-1) transition(p,S)|| <= 8.
```

The bound is intentionally `8`, not `1`.  The reverse transition is the
contraction; scalar-normalized forward recovery pays the inverse positive
Schur--Markov scalar.

## Producer consequence

The canonical transition witness now turns any uniform Julia co-defect factor
family with bound `B` into a uniform physical domination family with bound
`8B`.  This removes the norm-normalization blocker from the active route.  It
does not construct the uniform co-defect factor family itself, identify the
completed-history readout, or prove Gate 3U, the finite-S sign, Burnol's
identity, or RH.

## Lean owner and audit

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaJointProducer.lean
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaJointProducerAudit.lean
```

The new declarations are audited against the repository baseline
`[propext, Classical.choice, Quot.sound]`.
