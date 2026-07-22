# Proof 479: reflected second-support root energy

## Result

The result is good: Proof 478's compact support energy now reaches the actual
source second-support carrier. It does not yet close Gate 3U or RH.

The reflected branch is transported in two stages:

```text
compact pair for g(-x)
  -> radial translations by +/- log(lambda)
  -> archimedean Hardy--Titchmarsh unitary
  -> sourceSecondSupportCompactRootPairData.
```

Every transport has operator norm at most one. Therefore both actual legs
satisfy

```text
sum_i norm(leg e_i)^2
  <= (c-a)^2 * seminorm_0,0(g.reflection)^2.
```

Lean also proves directly from the defining seminorm inequalities that

```text
seminorm_0,0(g.reflection) = seminorm_0,0(g).
```

Thus both actual second-support legs obey the same original-root polynomial
as the outer pair. No renewal index or finite visible prime family appears in
this bound.

## Boundary

The remaining substantial term in Proof 477's fixed physical energy is the
prolate commutator energy, followed by the direct-sum energy bookkeeping that
recombines all three physical branches.

No renewal/basis sum exchange, canonical Gate 3U polynomial, finite-S sign,
negative-owner integration, Burnol identity, or
`_root_.RiemannHypothesis` is proved here.
