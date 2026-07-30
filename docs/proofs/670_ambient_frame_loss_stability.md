# Proof 670: ambient frame-loss stability

## Result

The result is good as a route decomposition, but it does not close the
factor gate. Proof 670 isolates one sufficient quantitative input which,
together with the restricted raw Bone 1 estimate, produces Proof 648's full
ambient-loss quotient. The constants compose exactly by multiplication.

```text
restricted raw Bone 1 bound B
  + route-uniform frame-loss stability K
  -> full ambient-loss factor bound B*K
  -> Proof 669 two-step factor bound B*K
  -> paired finite-horizon envelope.
```

Neither the restricted raw bound nor the actual frame-loss stability theorem
is constructed here. Bone 1A, the ambient quotient, Gate 3U, the finite-S
sign, Burnol's identity, and RH remain open.

## The missing projection step

For one route-valid pair `(p,S)`, write

```text
A_p     =(primeEulerAmbientLossFactor p)^dagger,
F_S     =newSuffixFrame unitSoninScale S,
I_(p,S) =signedCompressedInteriorOwner_(p,S),
C_(p,S) =suffixActualBandCompleteCoupledAmbientTarget_(p,S).
```

The actual frame is isometric, so `F_S^dagger F_S=I`. The canonical ambient
target is

```text
C_(p,S)=I_(p,S) F_S^dagger.
```

The restricted raw Bone 1 predicate only controls vectors before they enter
the ambient carrier:

```text
||I_(p,S)x||^2 <= B^2 ||A_p F_S x||^2.
```

Because `B>=0`, Lean first converts this to the unsquared norm inequality

```text
||I_(p,S)x|| <= B ||A_p F_S x||.
```

For an arbitrary ambient vector `u`, setting `x=F_S^dagger u` leaves one
extra orthogonal frame projection `F_S F_S^dagger` inside the loss:

```text
||C_(p,S)u||
  = ||I_(p,S)F_S^dagger u||
  <= B ||A_p F_S F_S^dagger u||.
```

Proof 670 names the required frame-loss stability (frame-loss stability):

```text
||A_p F_S F_S^dagger u|| <= K ||A_p u||,
```

with one `K` shared by every route-valid `(p,S)`. Combining the two estimates
gives the exact ambient domination

```text
||C_(p,S)u|| <= (B*K) ||A_p u||.
```

```text
 source x                 ambient u
    |                         |
    v                         v
   F_S                    F_S F_S^dagger
    |                         |
    +-----------> A_p <-------+
    |                         |
 raw bound B          stability bound K
    |                         |
    +------------+------------+
                 v
       ambient domination B*K
```

## Douglas handoff

The existing Douglas factor theorem applies directly to the last
same-vector norm inequality. It constructs a continuous linear map
`R_(p,S)` satisfying

```text
R_(p,S) A_p=C_(p,S),
||R_(p,S)||<=B*K.
```

This is exactly `SuffixCompleteCoupledAmbientLossFactorData`. Quantifying the
construction over the route produces

```text
SuffixCompleteCoupledRouteUniformAmbientLossFactor owner (B*K).
```

Proof 669 then converts it, without changing the constant, into

```text
SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
  owner (B*K).
```

No approximate-kernel limit, compactness argument, or horizon truncation is
used in this bridge.

## Why stability is not automatic

Proof 670 also formalizes a two-coordinate Hilbert-space guard. Let

```text
H=WithLp 2 (Complex x Complex),
F x=(x,0),
F^dagger(x,z)=x,
A_epsilon(x,z)=(x+z,epsilon*z),
C=F^dagger.
```

For every `epsilon!=0`, the loss `A_epsilon` is injective. The frame has the
exact actual-route identity

```text
F^dagger F=I.
```

On the restricted frame range the bound is perfect:

```text
C(Fx)=x,
A_epsilon(Fx)=(x,0),
||C(Fx)||=||A_epsilon(Fx)||.
```

Now take the ambient cancellation vector

```text
u=(1,-1).
```

Then

```text
C u=1,
A_epsilon u=(0,-epsilon),
A_epsilon F F^dagger u=(1,0).
```

Both ambient domination and frame-loss stability therefore force

```text
1<=K*epsilon.
```

No `K` can work uniformly for all positive `epsilon`; choosing
`epsilon=(K+1)^(-1)` gives `K*epsilon<1`. Lean proves both nonexistence
statements.

```text
injective loss + F^dagger F=I + exact restricted bound
                              |
                              v
              does not imply uniform ambient control
```

This is a generic guard, not a no-go theorem for the actual finite-S owner.
The real-line translation and Sonin-frame geometry contain additional
structure absent from the two-coordinate family. Any actual proof must use
that structure explicitly.

## Active source problem

Up to the positive scalar in the prime Euler loss, the next estimate asks
whether the actual Sonin range projection preserves antiresonant
cancellation:

```text
||(I+U_(log p)) F_S F_S^dagger u||
  <= K ||(I+U_(log p))u||,
```

uniformly in every route-valid prime and suffix. In plain language, projecting
onto the moving Sonin frame must not turn an almost anti-periodic vector into
an order-one loss vector. Injectivity only says the denominator is never
exactly zero; it supplies no uniform lower scale.

The next producer should therefore study the actual commutator or graph-norm
geometry of `F_S F_S^dagger` against the prime-log translation while keeping
the complete cancellation intact. A generic compact approximate-kernel
argument cannot supply the required rate comparison.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorAmbientFrameLossStability.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorAmbientFrameLossStabilityAudit.lean
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
| Proof 670 focused source             |  3457 | PASS   |
| Proof 670 focused source + audit     |  3458 | PASS   |
| CCM25Concrete aggregate              |  3945 | PASS   |
| full repository                      |  4026 | PASS   |
+--------------------------------------+-------+--------+
```

All thirteen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, or new source linter warning
was added.
