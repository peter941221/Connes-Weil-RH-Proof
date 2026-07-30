# Proof 666: balanced polar first-jet recurrence

## Result

The result is good as a strict normal-form improvement, but it does **not**
close Bone 1A. Proof 665's unpolarized detector commutator is eliminated,
and the active column is rewritten as an exact recurrence on the old source
carrier.

Let

```text
K_S = unpolarized restricted Euler frame,
U_S = polar frame,
G_S = K_S^dagger K_S,
R_S = G_S^(-1/2),
L_S = R_S G_S,
D_S = U_S^dagger W U_S,
F_S = FirstJetPhysical_S,
B_0 = J^dagger W J.
```

The two metric gauges are exact inverses:

```text
R_S L_S = I,
L_S R_S = I.
```

Lean proves `L_S^dagger=L_S` without unfolding the continuous functional
calculus (continuous functional calculus, CFC) square root.

## Polar compression

The literal frame factorization is

```text
K_S = U_S L_S.
```

Therefore its detector compression satisfies

```text
A_S := K_S^dagger W K_S = L_S D_S L_S.
```

Multiplication by `R_S` on the appropriate side cancels one `L_S` factor:

```text
A_S R_S - R_S A_S
  = L_S D_S - D_S L_S.
```

Proof 665's physical cocycle consequently becomes

```text
Z_S
  = F_S L_S
    + (L_S D_S-D_S L_S)
    + (L_S B_0-B_0 L_S)

  = F_S L_S + [L_S,D_S+B_0].
```

Here `[X,Y]=XY-YX` is a commutator (commutator). The two detector terms are
combined before any norm is taken.

```text
 +-----------------------+       +-----------------------+
 | unpolarized term      |       | polar frame identity  |
 | [K^dagger W K, R]     |       | K = U L               |
 +-----------+-----------+       +-----------+-----------+
             |                               |
             +---------------+---------------+
                             v
                   [L D L, R] = [L,D]
                             |
                             v
                  Z = F L + [L,D+B_0]
```

## Old-carrier recurrence

Define the complete adjacent transition gauge and first-jet defect by

```text
H_(p,S) = L_(p::S) R_S,
P_S     = B_0 + D_S - F_S.
```

The actual compressed Schur transition `T_(p,S)` obeys

```text
H_(p,S) = (1+q_p) T_(p,S),
H_(p,S) L_S = L_(p::S).
```

The single-suffix cocycle also has the factorization

```text
Z_S = L_S(D_S+B_0)-P_S L_S.
```

Substitution into Proof 665's adjacent column cancels both endpoint gauges
and gives the main identity:

```text
[Z_(p::S)-H_(p,S)Z_S]R_S
  = H_(p,S)P_S
    -P_(p::S)H_(p,S)
    +L_(p::S)(D_(p::S)-D_S)R_S.
```

The Lean proof isolates this as a generic noncommutative-ring identity
(noncommutative ring identity). This matters because the cancellation follows
only from associativity plus `R_S L_S=L_S R_S=I`; it is not an artifact of a
large simplifier call.

The transition factor itself is harmless:

```text
||H_(p,S)||
  = ||(1+q_p)T_(p,S)||
  <= 2,
```

using `0<=q_p<1` and `||T_(p,S)||<=1`.

## Bone 1A readback

The theorem
`routeScaledBalancedPhysicalCocycleColumn_eq_polarFirstJetRecurrence`
identifies the Proof 665 route column with the recurrence column as operators.
Consequently
`exists_routeUniformScaledCompleteTargetBound_iff_polarFirstJetRecurrence`
proves, with the same constant,

```text
Bone 1A route-uniform bound exists
  <->
sup_(route-valid p,S) q_p^(-1/2)
  ||H_(p,S)P_S-P_(p::S)H_(p,S)
    +L_(p::S)(D_(p::S)-D_S)R_S|| < infinity.
```

This is the new active bottom. The three summands must remain in their signed
combination. The bound `||H_(p,S)||<=2` does not justify estimating the two
`P` terms and the polar detector increment separately; such a split would
discard the recurrence cancellation that the proof was built to expose.

Proof 656's two-step factor remains a separate Bone 1 requirement. Gate 3U,
the finite-S sign, Burnol's identity, and RH also remain open.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedPolarFirstJetRecurrence.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedPolarFirstJetRecurrenceAudit.lean
```

## Verification

The Windows truth source was copied to the Ubuntu-24.04 WSL2 ext4 mirror and
built under the shared Lake lock.

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 666 focused source + audit     |  3454 | PASS   |
| CCM25Concrete aggregate              |  3941 | PASS   |
| full repository                      |  4022 | PASS   |
+--------------------------------------+-------+--------+
```

All thirteen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, or new source linter warning was added.
