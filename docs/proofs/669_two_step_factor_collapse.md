# Proof 669: two-step factor collapse

## Result

The result is good as an algebraic route simplification. Proof 656's
two-step coboundary factor (two-step coboundary factor) and Proof 648's
ambient-loss quotient (ambient-loss quotient) are the same contract with the
same norm bound. Consequently, the separately supplied horizon-one size gate
is redundant whenever the two-step factor exists.

This does not construct the factor. The route-uniform ambient-loss quotient,
the raw Bone 1A bound, Gate 3U, the finite-S sign, Burnol's identity, and RH
remain open.

Proof 670 later gives a sufficient decomposition of this factor gate: a
restricted raw Bone 1 bound `B` plus route-uniform frame-loss stability `K`
constructs the ambient quotient, and hence this two-step factor, with bound
`B*K`. It also proves by an injective two-coordinate model that the stability
input does not follow from the isometric-frame identities alone.

## No fixed translation vectors

Let `U_a` be the genuine whole-line logarithmic translation and let `a>0`.
If `U_a x=x`, the additive representation gives

```text
U_(N a)x=x
```

for every natural number `N`. The existing weak-escape theorem (weak escape)
simultaneously gives

```text
<U_(N a)x,x> -> 0.
```

The left side is the constant `||x||^2`, so `x=0`. Applying `U_a` also turns
a fixed vector of `U_(-a)` into a fixed vector of `U_a`. Lean therefore
proves

```text
ker(I-U_(-a))={0}.
```

Equivalently, the one-step coboundary is injective and can be cancelled from
the left.

```text
 U_a x=x
     |
     +----> U_(N a)x=x ----> <U_(N a)x,x>=||x||^2
                                      |
 weak escape -------------------------+----> ||x||^2=0
                                                    |
                                                    v
                                                   x=0
```

The proof uses
`inner_cc20GlobalLogTranslation_nat_mul_tendsto_zero`; it does not assume a
spectral gap or bounded inverse for `I-U_(-a)`.

## Exact factor cancellation

The additive translation law gives the operator identity

```text
I-U_(-2a)=(I-U_(-a))(I+U_(-a)).
```

Write

```text
a       =log p,
s_p     =primeEulerAmbientLossScale p,
C_(p,S) =suffixActualBandCompleteCoupledAmbientTarget_(p,S).
```

Proof 656's factor contract is

```text
s_p^(-1)(I-U_(-a))C_(p,S)^dagger
  =(I-U_(-2a))R_(p,S).
```

Substituting the two-step identity exposes the same injective left factor on
both sides:

```text
(I-U_(-a))[s_p^(-1)C_(p,S)^dagger]
  =(I-U_(-a))[(I+U_(-a))R_(p,S)].
```

Legal left cancellation gives

```text
s_p^(-1)C_(p,S)^dagger
  =(I+U_(-a))R_(p,S).
```

After multiplying by `s_p` and taking adjoints, this is exactly Proof 648's
ambient-loss factorization:

```text
R_(p,S)^dagger (primeEulerAmbientLossFactor p)^dagger
  =C_(p,S).
```

The reverse conversion takes the adjoint factor and restores the one-step
coboundary. Both directions preserve the factor norm because
`||R^dagger||=||R||`.

## Route-uniform equivalence

Lean proves, for every owner and the same real constant `B`,

```text
SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor owner B
  <->
SuffixCompleteCoupledRouteUniformAmbientLossFactor owner B.
```

It also proves the corresponding existential equivalence without changing
the constant.

```text
+------------------------------+       +------------------------------+
| Proof 656 two-step factor B  | <===> | Proof 648 ambient quotient B |
+---------------+--------------+       +---------------+--------------+
                |                                      |
                +------------------+-------------------+
                                   v
                    finite-horizon readout <= 2B
                                   |
                          choose horizon N=1
                                   v
                    horizon-one target size <= 2B
```

Therefore one route-uniform two-step factor bound alone reaches:

```text
scaled target size bound with constant 2B
  -> paired adjoint-coboundary envelope
  -> pointwise finite-horizon readout bound
  -> raw Bone 1 consumer
  -> renewed Bone 1 consumer.
```

The logical direction matters. A horizon-one size bound still does not
produce a two-step factor. Proof 669 proves `factor -> size`, not
`size -> factor`.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorTwoStepFactorCollapse.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorTwoStepFactorCollapseAudit.lean
```

The aggregate import is owned by
`ConnesWeilRH/Source/CCM25Concrete.lean`.

## Verification

The Windows truth source was copied to the Ubuntu-24.04 WSL2 ext4 mirror and
built under the shared Lake lock.

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 669 focused source + audit     |  3457 | PASS   |
| CCM25Concrete aggregate              |  3944 | PASS   |
| full repository                      |  4025 | PASS   |
+--------------------------------------+-------+--------+
```

All seventeen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, or new source linter warning
was added.
