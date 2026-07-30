# Proof 631: fixed-step compactness

## Result

Proof 631 strengthens Proof 629 at every fixed `(p,S)` on the unit Sonin
carrier.  Let

```text
D_(p,S) = (N_p^dagger - rho_p I) newFrame_(p,S),
K_(p,S) = R_(p,S)^dagger B_S - B_(p::S) R_(p,S)^dagger.
```

Lean proves:

```text
D_(p,S) is injective,
K_(p,S) is compact.
```

Consequently, for every bounded source sequence `x_n`,

```text
D_(p,S) x_n -> 0  ==>  K_(p,S) x_n -> 0.
```

The prime and suffix are fixed in this implication.

## Proof mechanism

The generic functional-analytic layer proves that a bounded approximate
kernel of an injective Hilbert-space operator is weakly null.  Indeed,
injectivity of `D` makes `range(D^dagger)` dense, so convergence against
vectors of the form `D^dagger y` extends to every fixed test vector.  A
compact operator maps a weakly null bounded sequence to a norm-null sequence.

The concrete compactness proof retains the complete signed owner.  Existing
Hilbert--Schmidt pair data makes the local raw defect `L_(p,S)^dagger`
compact, while Proof 623 gives

```text
K_(p,S) T_(p,S)^dagger = -L_(p,S)^dagger.
```

Postcomposing by `R_(p,S)^dagger` and using

```text
T_(p,S)^dagger R_(p,S)^dagger = rho_p I,
rho_p != 0,
```

recovers compactness of `K_(p,S)`.  At unit scale, compact support supplies
the boundary intervals and the strict prolate theorem supplies the missing
Hilbert--Schmidt summability witness.

```text
 local A^dagger B pair
          |
          v
 L_(p,S)^dagger compact
          |
          v  K T^dagger = -L^dagger
 rho_p K compact
          |
          v  rho_p != 0
 K_(p,S) compact
```

## Boundary

This does not prove a relative rate

```text
||K_(p,S)x|| <= C ||D_(p,S)x||.
```

Both sides may tend to zero while their ratio diverges.  It also does not
control a moving sequence `(p_n,S_n)`.  Thus any remaining fixed-step
obstruction is a rate obstruction, and any family obstruction may still move
through the route.

## Lean owners

```text
ConnesWeilRH/Source/CC20Concrete/CompactApproximateKernel.lean
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorFixedStepCompactness.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorFixedStepCompactnessAudit.lean
```

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| fixed-step compactness source        |  3413 | PASS   |
| focused seven-declaration audit      |     - | PASS   |
| CCM25Concrete aggregate              |  3909 | PASS   |
| full repository                      |  3990 | PASS   |
+--------------------------------------+-------+--------+
```

All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
