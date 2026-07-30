# Proof 671: frame-loss commutator reduction

## Result

The result is good as an exact reduction, but it does not close the factor
gate. Proof 671 identifies Proof 670's frame-loss stability with one concrete
relative commutator estimate for the actual prime-log translation and the
actual semilocal Sonin projection.

```text
relative translation/Sonin commutator bound L
  -> frame-loss stability bound L+1
  -> raw Bone 1 bound B times ambient factor B*(L+1)
  -> Proof 669 two-step factor with the same bound
  -> paired finite-horizon envelope.
```

Conversely, frame-loss stability with bound `K` gives the relative
commutator bound `K+1`. Thus the existence of either route-uniform bound is
equivalent. The module does not construct either bound. The restricted raw
Bone 1 estimate, the actual relative commutator estimate, Bone 1A, Gate 3U,
the finite-S sign, Burnol's identity, and RH remain open.

## The actual objects

For a visible prime `p` and suffix `S`, write

```text
U_p =U_(log p),
Q_p =I+U_p,
s_p =primeEulerAmbientLossScale p,
P_S =newSuffixRangeProjection unitSoninScale S.
```

The existing source theorems identify the ambient loss and the projection
without introducing a surrogate carrier:

```text
(primeEulerAmbientLossFactor p)^dagger=s_p Q_p,

P_S
  =parameterizedCanonicalGramProjection unitSoninScale 1 S
  =starProjection_(ccm24SemilocalSoninClosedSubspace unitSoninScale S).
```

The real scalar `s_p` is positive. It therefore cancels from the same-vector
norm comparison, so Proof 670's stability predicate is exactly

```text
||Q_p P_S u||<=K||Q_p u||.
```

Because `P_S` is an orthogonal projection (orthogonal projection), it is
contractive:

```text
||P_S v||<=||v||.
```

These identities are proved by
`ambientLossProjection_domination_iff_core`,
`newSuffixRangeProjection_eq_semilocalSoninStarProjection`, and
`norm_newSuffixRangeProjection_apply_le` in the Proof 671 source module.

## Exact commutator split

The project convention is

```text
[A,P]=A P-P A.
```

Since the identity commutes with every projection,

```text
[Q_p,P_S]=[I+U_p,P_S]=[U_p,P_S].
```

Proof 671 names this actual relative commutator (relative commutator) as

```text
C_(p,S)=[U_p,P_S]
```

and proves the pointwise identities

```text
Q_p P_S u=C_(p,S)u+P_S Q_pu,

C_(p,S)u=Q_p P_Su-P_S Q_pu.
```

The first identity plus projection contractivity gives

```text
||C_(p,S)u||<=L||Q_pu||
  ->
||Q_pP_Su||
  <=||C_(p,S)u||+||P_SQ_pu||
  <=(L+1)||Q_pu||.
```

The reverse identity gives

```text
||Q_pP_Su||<=K||Q_pu||
  ->
||C_(p,S)u||
  <=||Q_pP_Su||+||P_SQ_pu||
  <=(K+1)||Q_pu||.
```

Hence the constants change only by the unavoidable contractive copy of
`P_SQ_pu`:

```text
+-----------------------------+-----------------------------+
| input                       | output                      |
+-----------------------------+-----------------------------+
| relative commutator L       | frame-loss stability L+1    |
| frame-loss stability K      | relative commutator K+1     |
+-----------------------------+-----------------------------+
```

The theorem
`exists_routeUniformAmbientFrameLossStability_iff_relativeCommutatorDomination`
packages the two directions as an existential equivalence.

## Why an ordinary commutator bound is insufficient

Unitarity of `U_p` and contractivity of `P_S` give only the ambient estimate

```text
||[U_p,P_S]u||<=2||u||.
```

The route needs the strictly different graph-norm estimate

```text
||[U_p,P_S]u||<=L||(I+U_p)u||.
```

The right side can be arbitrarily small on antiresonant approximate-kernel
vectors, while `||u||` stays bounded. Thus the ordinary operator norm does
not provide the required comparison. The proof must show that the actual
Sonin commutator inherits the same antiresonant cancellation, not merely
that it is bounded on the ambient Hilbert space.

```text
 ambient boundedness                    required relative boundedness

 ||[U,P]u|| <= 2||u||                  ||[U,P]u|| <= L||(I+U)u||
          |                                         |
          +---- no spectral-gap bridge -------------+
```

This is the exact obstruction already visible in Proof 670's two-coordinate
guard, now attached to the real translation/Sonin source object.

## Consumer handoff

If the restricted raw Bone 1 estimate has constant `B` and the relative
commutator estimate has constant `L`, Proof 671 constructs

```text
SuffixCompleteCoupledRouteUniformAmbientLossFactor owner (B*(L+1)).
```

Proof 669 then gives

```text
SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
  owner (B*(L+1))
```

and the paired adjoint-coboundary envelope. The direct consumers are
`routeUniformAmbientLossFactorOfRawAmbientDominationAndRelativeCommutator`,
`routeUniformTwoStepFactorOfRawAmbientDominationAndRelativeCommutator`, and
`pairedAdjointCoboundaryEnvelopeBoundOfRawAmbientDominationAndRelativeCommutator`.

No estimate is lost beyond the single `+1` required by the projection term.

## Active source problem

The next producer has one precise target:

```text
sup over route-valid (p,S) and nonzero u of

  ||[U_(log p),P_S]u|| / ||(I+U_(log p))u||

must be finite.
```

The useful divide-and-conquer order is:

```text
1. expand P_S through the genuine semilocal Sonin support/Fourier owner;
2. keep the outer-support, Fourier-support, and prolate correction signed;
3. test the complete commutator on the known antiresonant approximate kernel;
4. prove the relative bound, or produce an actual finite-S counterexample;
5. only then feed the result into the B*(L+1) consumer.
```

Separate operator-norm estimates of the support branches cannot prove the
target because they discard the denominator's cancellation before the
branches recombine.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorFrameLossCommutatorReduction.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorFrameLossCommutatorReductionAudit.lean
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
| Proof 671 focused source             |  3458 | PASS   |
| Proof 671 focused source + audit     |  3459 | PASS   |
| CCM25Concrete aggregate              |  3946 | PASS   |
| full repository                      |  4027 | PASS   |
+--------------------------------------+-------+--------+
```

All fourteen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, or new source linter warning
was added.
