# Proof 511: reverse Julia recovery and the joint-producer boundary

## Result

Proof 511 closes the exact reverse direction left open by Proof 510.  If a
local mismatch has the genuine co-defect factorization

```text
LocalMismatch(p,S)
  = LeftJuliaCoDefect(p,S) * RightFactor(p,S)
||RightFactor(p,S)|| <= bound,
```

then the one-sided physical mismatch is controlled with the explicit factor

```text
||(primeSchurMarkovScalar p)^(-1) * transition(p,S)||.
```

The result is handed back to the physical ambient-plus-boundary domination
owner.  At family level, an additional common bound for these
scalar-normalized forward transitions recovers Proof 509's uniform physical
domination contract.

## What remains open

The transition-bound structure is an explicit producer obligation.  It is not
derived from the contractive reverse transition: the forward recovery is
scalar-normalized and its norm is not available here as a family-independent
contraction.  Therefore Proof 511 does not manufacture the missing source
theorem, completed-history readout identity, Gate 3U bound, finite-S sign,
Burnol identity, or unconditional RH.

The exact dependency is:

```text
uniform Julia co-defect factors
        |
        |  needs a uniform scalar-normalized forward-transition bound
        v
uniform physical domination
        |
        v
Proof 509/510 physical readout and Julia factors
```

This keeps the forward/reverse norm loss visible instead of treating a local
factor family as if it were already the missing source-specific producer.

## Lean owner and audit

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaJointProducer.lean
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaJointProducerAudit.lean
```

The focused declarations are axiom-clean with the repository baseline
`[propext, Classical.choice, Quot.sound]`.  The finite-S sign, Burnol identity,
and `_root_.RiemannHypothesis` remain open.
